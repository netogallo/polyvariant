{-# Language RecordWildCards, GADTs, TupleSections, MultiParamTypeClasses #-}
module Analysis.Types.Annotation where
import qualified Analysis.Types.Sorts as S
import qualified Data.Set as D
import Analysis.Common
import qualified Data.Map as M
import Data.Maybe
import Control.Applicative
import Control.Monad.Identity
import Control.Monad (liftM)
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
  deriving (Show,Read)

instance C.LambdaCalculus Annotation Algebra where
  lambdaDepths = depths
  foldM = foldAnnM
  byId = undefined

data Algebra m a =
  Algebra {
    fvar :: Int -> Int -> m a,
    fabs :: Int -> S.FlowVariable -> a -> m a,
    flabel :: Int -> String -> m a,
    funion :: Int -> a -> a -> m a,
    fapp :: Int -> a -> a -> m a
    }


instance Eq Annotation where
  x == y = evalState (equiv x y) (ix + 1)
    where
      equiv x' y' =
        case (x',y') of
          (Var i,Var j) -> return (i == j)
          ((Union a b), Union a' b') -> (&&) <$> equiv a a' <*> equiv b b'
          (App a b, App a' b') -> (&&) <$> equiv a a' <*> equiv b b'
          (Empty, Empty) -> return True
          (Label i, Label j) -> return (i == j)
          (Abs v1 e,Abs v2 e') | v1 == v2 -> equiv e e'
          (Abs v1 e,Abs v2 e') | S.sort v1 == S.sort v2 -> do
            i <- get
            put (i + 1)
            equiv (rename (M.fromList [(S.name v1,i)]) e) (rename (M.fromList [(S.name v2,i)]) e')
          (Set exps, Set exps') | D.size exps == D.size exps' ->
            foldM (\s (e,e') -> (&& s) <$> equiv e e') True $ zip (D.toAscList exps) (D.toAscList exps')
          _ -> return False
          
      ix = max (maxIx x) (maxIx y)

instance Ord Annotation where

  compare x' y' = evalState (compare' x' y') (ix + 1)
    where
      ix = max (maxIx x') (maxIx y')
      compare'' EQ b = b
      compare'' a _ = a
      compare' x y =
        case (x,y) of
          (Var i,Var j) -> return $ compare i j
          (Union a b,Union a' b') -> compare'' <$> compare' a a' <*> compare' b b'
          (App a b,App a' b') -> compare'' <$> compare' a a' <*> compare' b b'
          (Label i,Label j) -> return $ compare i j
          (Empty, Empty) -> return EQ
          (Abs v1 e, Abs v2 e') | v1 == v2 -> compare' e e'
          (Abs v1 e, Abs v2 e') | S.sort v1 == S.sort v2 -> do
            i <- get
            put (i+1)
            compare' (rename (M.fromList [(S.name v1,i)]) e) (rename (M.fromList [(S.name v2,i)]) e')
          (Set es, Set es') -> do
            let
              la = D.toAscList es
              lb = D.toAscList es'
              cata EQ (e,e') = compare' e e'
              cata r _ = return r
            r1 <- foldM cata EQ $ zip la lb
            case r1 of
              EQ | D.size es > D.size es' -> return GT
              EQ | D.size es < D.size es' -> return LT
              r -> return r
            
          (Abs v1 _, Abs v2 _) -> return $ compare v1 v2
          (Empty,_) -> return LT
          (_,Empty) -> return GT
          (Var _,_) -> return LT
          (_,Var _) -> return GT
          (Label _,_) -> return LT
          (_,Label _) -> return GT
          (Abs _ _,_) -> return LT
          (_,Abs _ _) -> return GT
          (App _ _,_) -> return LT
          (_,App _ _) -> return GT
          (Union _ _,_) -> return LT
          (_,Union _ _) -> return GT

maxIx ann = maximum $ D.toList $ D.map fst $ vars ann

data ReduceContext = ReduceContext{
  freshIx :: Int
  }

algebra :: Monad m => Algebra m Annotation
algebra = Algebra{
  fvar = \_ x -> return $ Var x,
  fabs = \_ v s -> return $ Abs v s,
  flabel = \_ l -> return $ Label l,
  funion = \_ a b -> return $ Union a b,
  fapp = \_ a b -> return $ App a b
  }

fresh :: Monad m => StateT ReduceContext m Int
fresh = do
  ctx <- get
  put $ ctx{freshIx = freshIx ctx + 1}
  return $ freshIx ctx

foldAnnM f@Algebra{..} s0 a0 = evalStateT (foldAnnM' s0 a0) 0
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
        Empty -> return s

depths = runIdentity . (foldAnnM alg M.empty) 
  where
    alg = Algebra {
      fapp = un,
      funion = un,
      fabs = \i _ m -> return $ M.insert i 0 $ M.map (+1) m,
      flabel = sing,
      fvar = sing
      }
    sing i _ = return $ M.insert i 0 M.empty
    un i ma mb = return $ M.insert i 0 $ M.union ma mb

bound (_,b) = b == C.Bound
    
vars = runIdentity . (foldAnnM alg (D.empty :: D.Set (Int,C.Boundness)))
  where
    alg = Algebra {
      fvar = const fvar,
      fabs = const fabs,
      flabel = const $ const $ return D.empty,
      funion = const funion,
      fapp = const funion
      }
    funion a b = return $ D.union a b
    fvar v = return $ D.singleton (v,C.Free)
    fabs v s =
      let
        bounder (v',boundness)
          | S.name v == v' = (v',C.Bound)
          | otherwise = (v',boundness)
      in return $ D.insert (S.name v, C.Bound) $ D.map bounder s

renameByLambdasOffset base offset obj = lift calcReplacements  >>= mkReplacements
  where
    calcReplacements = foldAnnM repAlg M.empty obj
    repAlg = Algebra{
      fvar = C.discard $ C.rename base,
      flabel = C.discard $ C.rename base,
      funion = C.rename2 base,
      fapp = C.rename2 base,
      fabs = C.renameAbs base offset obj
      }
    subAlg rep = algebra{
      fvar = C.subVar Var rep,
      fabs = C.subAbs Abs rep
      }
    mkReplacements rep = foldAnnM (subAlg rep) Empty obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int,M.empty)

subAppAnn cons obj rep i s ann = do
  let offset' = fromJust $ M.lookup i $ C.lambdaDepths obj
  ann' <- renameByLambdasOffset (fromJust $ M.lookup i rep) offset' ann
  return $ cons s ann'


rename ren = runIdentity . (foldAnnM alg Empty)
  where
    alg = algebra{
      fvar = const fvar,
      fabs = const fabs
      }
    fvar v = return $ Var $ M.findWithDefault v v ren
    fabs v s = return $ Abs v{S.name=M.findWithDefault (S.name v) (S.name v) ren} s

replace rep = runIdentity . (foldAnnM alg Empty)
  where
    alg = algebra{
      fvar = const $ \v -> return $ M.findWithDefault (Var v) v rep
      }

-- Increase or decrease the `depth` of all bound variables in the expression
increment i ann = runIdentity $ foldAnnM (alg $ D.map fst $ D.filter bound $ vars ann) Empty ann
  where
    fvar vars _ v
      | D.member v vars = return $ Var $ v + i
      | otherwise = return $ Var v
    fabs vars _ v s
      | D.member (S.name v) vars = return $ Abs v{S.name = i + S.name v} s
      | otherwise = return $ Abs v s
    alg vars = algebra{
      fvar = fvar vars,
      fabs = fabs vars
      }

application fun@(Abs var a1) a2 =
  increment (-1) $ runIdentity $ foldAnnM (alg $ depths a1) Empty a1
  where
    a2' = increment 1 a2
    fvar depths i v
      | S.name var == v =
        let d = M.lookup i depths
        in case d of
          Just d' | d' > 0 -> return $ increment d' a2'
          Just _ -> return a2'
          Nothing -> fail "No depth for expression!"
      | otherwise = return $ Var v
    alg depths = algebra{
      fvar = fvar depths
      }
application a1 a2 = App a1 a2

-- application :: (Monad m, Functor m) => Annotation -> Annotation -> StateT ReduceContext m Annotation
-- application (Abs v a1) a2 = do
--   a1' <- (flip rename a1) . M.fromList <$> mapM (\v' -> (v',) <$> fresh) newVars
--   return $ replace (M.fromList [(S.name v,a2)]) a1'

--   where
--     varsA1 = D.map fst $ vars a1
--     freeA2 = D.map fst $ D.filter ((== Free) . snd) $ vars a2
--     newVars = D.toList $ D.intersection varsA1 freeA2
-- application a1 a2 = return $ App a1 a2

reduce' = runIdentity . (foldAnnM alg Empty)
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
  unions $ reduce $ renameByLambdas ann
  
recombine (Var s) = D.singleton $ Var s
-- recombine (App (Abs v ann) ann2) = cartesian App (recombine ann1) (recombine ann2)
recombine (App ann1 ann2) = cartesian App (recombine ann1) (recombine ann2)
recombine (Abs v ann) = D.map (Abs v) $ recombine ann

