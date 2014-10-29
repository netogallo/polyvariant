{-# Language RecordWildCards, MultiParamTypeClasses #-}
module Analysis.Types.Effect where
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S
import qualified Data.Set as D
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad.Identity
import qualified Analysis.Types.Common as C
import Data.Maybe (fromJust)
import Control.Applicative
import Debug.Trace

data Effect =
  Var Int
  | App Effect Effect
  | AppAnn Effect A.Annotation
  | Abs S.FlowVariable Effect
  | Union Effect Effect
  | Flow String A.Annotation
  | Empty
  | Set (D.Set Effect)
  deriving (Show,Read,Ord,Eq)

instance C.Fold Effect Algebra where
  foldM = foldEffectM
  byId = undefined
  baseAlgebra = algebra
  groupAlgebra =
    Algebra {
      fvar = \_ _ -> return C.void,
      fapp = \_ s1 s2 -> return $ s1 C.<+> s2,
      fappAnn = \_ a _ -> return a,
      fabs = \_ _ s -> return s,
      funion = \_ a b -> return $ a C.<+> b,
      fflow = \_ _ _ -> return C.void,
      fempty = \_ -> return C.void
      }

instance C.WithAbstraction Effect Algebra where
  abst (Abs v e) = Just (v,e)
  abst _ = Nothing
  abstC = Abs
  increment = increment
  vars = vars
  lambdaDepths = depths
  baseAbstAlgebra alg abst = alg{fabs=abst}
  groupAbstAlgebra alg abst = alg{fabs=abst}

instance C.LambdaCalculus Effect Algebra where
  app (App a1 a2) = Just (a1,a2)
  app _ = Nothing
  appC = App
  var (Var i) = Just i
  var _ = Nothing
  varC = Var
  baseCalcAlgebra alg var app = alg{
    fvar = var,
    fapp = app
    }
  groupCalcAlgebra alg var app = alg{fvar=var,fapp=app}

instance C.WithSets Effect Algebra where
  unionM (Union a b) = Just (a,b)
  unionM _ = Nothing
  unionC = Union

  setM (Set a) = Just a
  setM _ = Nothing
  setC = Set

  emptyM Empty = Just ()
  emptyM _ = Nothing
  emptyC = Empty

  unionAlgebra alg union void = alg{
    funion = union,
    fempty = void
    }

  groupUnionAlgebra alg union void =
    alg{
      funion = union,
      fempty = void
      }

data Algebra m t a =
  Algebra {
    fvar :: Int -> Int -> m a,
    fapp :: Int -> a -> a -> m a,
    fappAnn :: Int -> a -> A.Annotation -> m a,
    fabs :: Int -> S.FlowVariable -> a -> m a,
    funion :: Int -> a -> a -> m a,
    fflow :: Int -> String -> A.Annotation -> m a,
    fempty :: Int -> m a
    }

algebra :: Monad m => Algebra m Effect Effect
algebra = Algebra{
  fvar = \_ v -> return $ Var v,
  fapp = un App,
  funion = un Union,
  fabs = \_ v s -> return $ Abs v s,
  fflow = \_ lbl ann -> return $ Flow lbl ann,
  fappAnn = \_ s ann -> return $ AppAnn s ann,
  fempty = \_ -> return Empty
  }
  where
    un c _ a1 a2 = return $ c a1 a2

foldEffectM f@Algebra{..} a0 = evalStateT (foldEffectM' undefined a0) 0
  where
    foldEffectM' s a = do
      i <- get
      put (i+1)
      let
        go fn a1 a2 = do
          a1' <- foldEffectM' s a1
          a2' <- foldEffectM' s a2
          lift $ fn i a1' a2'
      case a of
        App a1 a2 -> go fapp a1 a2
        Union a1 a2 -> go funion a1 a2
        Set as -> foldEffectM' s $ foldl Union Empty $ D.toAscList as
        Var v -> lift $ fvar i v
        Abs v a1 -> (foldEffectM' s a1) >>= (lift . (fabs i v))
        AppAnn a1 a2 -> (foldEffectM' s a1) >>= \s' -> lift $ fappAnn i s' a2
        Flow l a1 -> lift $ fflow i l a1
        Empty -> lift $ fempty i

depths = runIdentity . (foldEffectM alg) 
  where
    alg = Algebra {
      fapp = un,
      funion = un,
      fabs = \i _ s -> return $ M.insert i 0 $ M.map (+1) s,
      fvar = sing,
      fappAnn = \i s _ -> return $ M.insert i 0 s,
      fflow = \i _ _ -> return $ M.insert i 0 M.empty,
      fempty = const (return M.empty)
      }
    sing i _ = return $ M.insert i 0 M.empty
    un i ma mb = return $ M.insert i 0 $ M.union ma mb


renameByLambdasOffset base' offset obj = lift calcReplacements >>= mkReplacements
  where
    base = M.map (\e -> (e,True)) base'
    d = depths obj
    repAlg = (C.baseRepAlg base' offset obj :: Algebra Identity Effect (M.Map Int (M.Map Int (Int,Bool)))){
      fflow = \i _ _ -> return $ M.fromList [(i,base)],
      fappAnn = \i e _ -> return $ M.insert i base $ e
      }
    calcReplacements = M.map (M.map fst) <$> foldEffectM repAlg obj
    renAnn rep i ann = A.renameByLambdasOffset (fromJust $ M.lookup i rep) (fromJust $ M.lookup i d) ann
    subAlg rep = (C.baseSubAlg rep){
      fappAnn = \i e ann -> AppAnn e <$> renAnn rep i ann,
      fflow = \i l ann -> Flow l <$> renAnn rep i ann
      }
    mkReplacements rep = foldEffectM (subAlg rep) obj


-- renameByLambdasOffset base offset obj = lift calcReplacements >>= mkReplacements
--   where
--     calcReplacements = foldEffectM repAlg obj
--     repAlg = Algebra{
--       fvar = C.discard $ C.rename base,
--       fapp = C.rename2 base,
--       fappAnn = \i s _ -> C.rename1 base i s,
--       fabs = C.renameAbs base offset obj,
--       funion = C.rename2 base,
--       fflow = C.discard $ C.discard $ C.rename base,
--       fempty = const (return M.empty)
--       }
--     subAlg rep =  algebra{
--       fvar = C.subVar Var rep,
--       fabs = C.subAbs Abs rep,
--       fappAnn = A.subAppAnn AppAnn obj rep
--       }
--     mkReplacements rep = foldEffectM (subAlg rep) obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int, M.empty)

vars :: Effect -> D.Set (Int,C.Boundness)
vars = runIdentity . C.foldM alg
  where
    flow _ s ann = return $ A.vars ann
    fappAnn _ eff ann = return $ D.union eff $ A.vars ann
    alg = (C.baseVarsAlg :: Algebra Identity Effect (D.Set (Int,C.Boundness))){
      fflow = flow,
      fappAnn = fappAnn
      }

increment i eff' = runIdentity $ C.foldM alg eff'
  where
    boundVars = D.filter C.bound $ vars eff'
    annIncrement = A.incrementWithBase boundVars
    appAnn _ eff ann = do
      let ann' = annIncrement i ann
      return $ AppAnn eff ann'
    flow _ l ann = do
      let ann' = annIncrement i ann
      return $ Flow l ann'
    alg = (C.baseIncAlg i $ D.map fst boundVars){
      fappAnn = appAnn,
      fflow = flow
      }

annApplication fun@(Abs v a1) a2 = increment (-1) $ runIdentity $ C.foldM alg a1
  where
    rep ann = 
      let annAlg = C.baseAppAlg (A.Abs v ann) a2
      in runIdentity $ C.foldM annAlg ann
    appAnn _ eff ann = do
      let ann' = rep ann
      return $ AppAnn eff ann'
    flow _ s ann =
      let ann' = rep ann
      in return $ Flow s ann'
    alg = algebra{
      fappAnn = appAnn,
      fflow = flow
      }

annApplication a1 a2 = AppAnn a1 a2

application fun@(Abs _ a1) a2 = increment (-1) $ runIdentity $ C.foldM (C.baseAppAlg fun a2) a1
application a1 a2 = App a1 a2

reduce' = runIdentity . foldEffectM alg
  where
    alg = algebra{
      fflow = \_ l ann -> return $ Flow l $ C.unions $ A.reduce ann,
      fapp = \_ e1 e2 -> let
         r = application e1 e2
         in
          return r,
          -- trace ("App: " ++ show (e1,e2,r)) $ return $ application e1 e2,
      fappAnn = \_ e1 ann -> let
        r = annApplication e1 ann
        in return $ case r of
          AppAnn eff ann' -> AppAnn eff $ A.reduce ann'
          _ -> r
               -- trace ("AApp: " ++ show (e1,ann,r)) $ return $ annApplication e1 ann
      }

reduce e = go e
  where
    go e =
      let e' = reduce' e
      in if e == e' then e else go e'    

normalize = C.unions . renameByLambdas . reduce . renameByLambdas
