{-# Language RecordWildCards, GADTs, TupleSections, MultiParamTypeClasses #-}
module Analysis.Types.Annotation where
import qualified Analysis.Types.Sorts as S
import qualified Data.Set as D
import Analysis.Common
import qualified Data.Map as M
import Data.Maybe
import Control.Monad.Identity
import Control.Monad.State
import qualified Analysis.Types.Common as C

data Annotation =
  Var Int
  | App Annotation Annotation
  | Union Annotation Annotation
  | Abs S.FlowVariable Annotation
  | Label String
  | Empty
  | Set (D.Set Annotation)
    -- Apparently the GHC derived Eq and Ord work well enough
    -- such that normalizing equivalent terms will reduce
    -- in equal terms
    -- For that property to hold, elements that have equal
    -- structure up to alpha renameing should be considered
    -- adjecent to the other acording to the Ord instance
  deriving (Show,Read,Eq,Ord)
           
instance C.Fold Annotation Algebra where
  foldM = foldAnnM
  byId = undefined

instance C.LambdaCalculus Annotation Algebra where
  lambdaDepths = depths
  app (App a1 a2) = Just (a1,a2)
  app _ = Nothing
  appC = App
  var (Var i) = Just i
  var _ = Nothing
  varC = Var
  abst (Abs v e) = Just (v,e)
  abst _ = Nothing
  abstC = Abs
  increment = increment
  baseAlgebra var abst app =
    algebra{fvar=var,fabs=abst,fapp=app}
  groupAlgebra var abst app =
    Algebra{
      fvar = var,
      fabs = abst,
      fapp = app,
      flabel = \_ _ -> return C.void,
      funion = \_  a b -> return $ a C.<+> b,
      fempty = const $ return C.void
    }

instance C.WithSets Annotation Algebra where
  unionM (Union a1 a2) = Just (a1,a2)
  unionM _ = Nothing
  unionC = Union
  setM (Set a) = Just a
  setM _ = Nothing
  setC = Set
  emptyM Empty = Just ()
  emptyM _ = Nothing
  emptyC = Empty
  unionAlgebra alg un empty = alg{funion=un,fempty=empty}
  

data Algebra m t a =
  Algebra {
    fvar :: Int -> Int -> m a,
    fabs :: Int -> S.FlowVariable -> a -> m a,
    flabel :: Int -> String -> m a,
    funion :: Int -> a -> a -> m a,
    fapp :: Int -> a -> a -> m a,
    fempty :: Int -> m a
    }

maxIx ann = maximum $ D.toList $ D.map fst $ vars ann

data ReduceContext = ReduceContext{
  freshIx :: Int
  }

algebra :: Monad m => Algebra m Annotation Annotation
algebra = Algebra{
  fvar = \_ x -> return $ Var x,
  fabs = \_ v s -> return $ Abs v s,
  flabel = \_ l -> return $ Label l,
  funion = \_ a b -> return $ Union a b,
  fapp = \_ a b -> return $ App a b,
  fempty = const (return Empty)
  }

fresh :: Monad m => StateT ReduceContext m Int
fresh = do
  ctx <- get
  put $ ctx{freshIx = freshIx ctx + 1}
  return $ freshIx ctx

foldAnnM f@Algebra{..} a0 = evalStateT (foldAnnM' undefined a0) 0
  where
    foldAnnM' s a = do
      i <- get
      put (i+1)
      let
        go fn a1 a2 = do
          a1' <- (foldAnnM' s a1)
          a2' <- (foldAnnM' s a2)
          lift $ fn i a1' a2'
      case a of
        App a1 a2 -> go fapp a1 a2
        Union a1 a2 -> go funion a1 a2
        -- Sets are treated as if they were unions
        Set as -> foldAnnM' s $ foldl Union Empty $ D.toAscList as
        Var v -> lift $ fvar i v
        Abs v a1 -> (foldAnnM' s a1) >>= (lift . (fabs i v))
        Label l -> lift $ flabel i l
        Empty -> lift $ fempty i

depths = runIdentity . (foldAnnM alg) 
  where
    alg = Algebra {
      fapp = un,
      funion = un,
      fabs = \i _ m -> return $ M.insert i 0 $ M.map (+1) m,
      flabel = sing,
      fvar = sing,
      fempty = const (return M.empty)
      }
    sing i _ = return $ M.insert i 0 M.empty
    un i ma mb = return $ M.insert i 0 $ M.union ma mb

vars :: Annotation -> D.Set (Int, C.Boundness)
vars = runIdentity . C.foldM alg
  where
--    alg :: Monad m => Algebra (StateT (D.Set (Int,C.Boundness)) m) Annotation (D.Set (Int,C.Boundness))
    alg = C.baseVarsAlg


renameByLambdasOffset base offset obj = lift calcReplacements  >>= mkReplacements
  where
    calcReplacements = foldAnnM repAlg obj
    repAlg = Algebra{
      fvar = C.discard $ C.rename base,
      flabel = C.discard $ C.rename base,
      funion = C.rename2 base,
      fapp = C.rename2 base,
      fabs = C.renameAbs base offset obj,
      fempty = const $ return M.empty
      }
    subAlg rep = algebra{
      fvar = C.subVar Var rep,
      fabs = C.subAbs Abs rep
      }
    mkReplacements rep = foldAnnM (subAlg rep) obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int,M.empty)

subAppAnn cons obj rep i s ann = do
  let offset' = fromJust $ M.lookup i $ C.lambdaDepths obj
  ann' <- renameByLambdasOffset (fromJust $ M.lookup i rep) offset' ann
  return $ cons s ann'


rename ren = runIdentity . (foldAnnM alg)
  where
    alg = algebra{
      fvar = const fvar,
      fabs = const fabs
      }
    fvar v = return $ Var $ M.findWithDefault v v ren
    fabs v s = return $ Abs v{S.name=M.findWithDefault (S.name v) (S.name v) ren} s

replace rep = runIdentity . (foldAnnM alg)
  where
    alg = algebra{
      fvar = const $ \v -> return $ M.findWithDefault (Var v) v rep
      }

-- Increase or decrease the `depth` of all bound variables in the expression
increment i ann = runIdentity $ foldAnnM alg ann
  where
    alg = C.baseIncAlg i $ D.map fst $ D.filter C.bound $ vars ann

application fun@(Abs _ a1) a2 = increment (-1) $ runIdentity $ C.foldM (C.baseAppAlg fun a2) a1
application a1 a2 = App a1 a2

reduce' = runIdentity . (foldAnnM alg)
  where
    alg = algebra{
      fapp = \i a1 a2 -> return $ application a1 a2
      }
    
reduce e = go e (reduce' e)
  where
    go x x'
      | x == x' = x
      | otherwise = go x' (reduce x')

unionGen empty singleton unions e =
  case e of
    Empty -> empty
    Union a1 a2 -> unions [(union' a1),(union' a2)]
    a -> singleton a
  where
    union' = unionGen empty singleton unions

union = unionGen D.empty D.singleton D.unions

unions e =
  case e of
    Union a1 a2 -> Set $ D.map unions (union e)
    App a1 a2 -> App (unions a1) (unions a2)
    Abs v a -> Abs v $ unions a
    Var v -> Var v
    Label s -> Set (D.singleton $ Label s)
    Empty -> Set (D.empty)
    a -> a

normalize :: Annotation -> Annotation
normalize ann =
  -- The second `renameByLambdas` is there only to ensure that all
  -- terms are equal to alpha renaming of the free variables
  C.unions $ reduce $ renameByLambdas ann
  
recombine (Var s) = D.singleton $ Var s
-- recombine (App (Abs v ann) ann2) = cartesian App (recombine ann1) (recombine ann2)
recombine (App ann1 ann2) = cartesian App (recombine ann1) (recombine ann2)
recombine (Abs v ann) = D.map (Abs v) $ recombine ann

