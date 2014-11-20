{-# Language MultiParamTypeClasses, FunctionalDependencies, RecordWildCards #-}
module Analysis.Types.LambdaCalc where
import qualified Analysis.Types.Common as C
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad.Identity
import Debug.Trace

data LambdaCalc t =
  Var Int
  | VFalse
  | VTrue
  | Abs (C.Variable t) (LambdaCalc t)
  | If (LambdaCalc t) (LambdaCalc t) (LambdaCalc t)
  | App (LambdaCalc t) (LambdaCalc t)
  | Fix (LambdaCalc t)
  deriving (Show,Read,Eq,Ord)

data Algebra t m t' a =
  Algebra{
    fvar :: Int -> Int -> m a,
    fvfalse :: Int -> m a,
    fvtrue :: Int -> m a,
    fabs :: Int -> (C.Variable t) -> a -> m a,
    fif :: Int -> a -> a -> a -> m a,
    fapp :: Int -> a -> a -> m a,
    ffix :: Int -> a -> m a
    }

algebra :: Monad m => Algebra t m (LambdaCalc t) (LambdaCalc t)
algebra = Algebra{
  fvar = \_ v -> return $ Var v,
  fvfalse = \_ -> return $ VFalse,
  fvtrue = \_ -> return $ VTrue,
  fabs = \_ var s -> return $ Abs var s,
  fif = \_ cond yes no -> return $ If cond yes no,
  fapp = \_ t1 t2 -> return $ App t1 t2,
  ffix = \_ t1 -> return $ Fix t1
  }

instance C.Fold (LambdaCalc t) (Algebra t) where
  byId = undefined
  foldM = foldLambdaCalcM
  baseAlgebra = algebra
  groupAlgebra =
    Algebra{
      fvar = \_ _-> return C.void,
      fvfalse = \_ -> return C.void,
      fvtrue = \_ -> return C.void,
      fabs = \_ _ s -> return s,
      fif = \_ cond yes no -> return $ cond C.<+> yes C.<+> no,
      fapp = \_ s1 s2 -> return $ s1 C.<+> s2,
      ffix = \_ s1 -> return s1
      }

groupAlgebraInit s0 =
    Algebra{
      fvar = \_ _ -> return s0,
      fvfalse = \_ -> return s0,
      fvtrue = \_ -> return s0,
      fabs = \_ _ s -> return s,
      fif = \_ cond yes no -> return $ cond C.<+> yes C.<+> no,
      fapp = \_ s1 s2 -> return $ s1 C.<+> s2,
      ffix = \_ s1 -> return s1
      }


-- instance C.LambdaCalculus (LambdaCalc t) (Algebra t) where
--   lambdaDepths = depths
--   app (App _ a1 a2) = Just (a1,a2)
--   app _ = Nothing
--   appC = undefined
--   var (Var i) = Just i
--   var _ = Nothing
--   varC = Var
--   abst (Abs _ v e) = undefined -- Just (v,e)
--   abstC = undefined
--   increment = undefined
--   baseAlgebra = undefined


foldLambdaCalcM Algebra{..} expr = evalStateT (foldLambdaCalcM' undefined expr) 0
  where
    foldLambdaCalcM' s l = do
      i <- get
      put (i + 1)
      case l of
        Var v -> lift $ fvar i v
        VFalse -> lift $ fvfalse i
        VTrue -> lift $ fvtrue i
        Abs var exp -> foldLambdaCalcM' s exp >>= lift . (fabs i var)
        If cond yes no -> do
          cond' <- foldLambdaCalcM' s cond
          yes' <- foldLambdaCalcM' s yes
          no' <- foldLambdaCalcM' s no
          lift $ fif i cond' yes' no'
        App exp1 exp2 -> do
          exp1' <- foldLambdaCalcM' s exp1
          exp2' <- foldLambdaCalcM' s exp2
          lift $ fapp i exp1' exp2'
        Fix exp -> foldLambdaCalcM' s exp >>= lift . (ffix i)

depths = runIdentity . (foldLambdaCalcM alg)
  where
    sing i = return $ M.fromList [(i,0 :: Int)]
    alg = Algebra{
      fvar = \i _ -> sing i,
      fvfalse = sing,
      fvtrue = sing,
      fabs = \i _ d -> return $ M.insert i 0 $ M.map (+1) d,
      fif = \i d1 d2 d3 -> return $ M.insert i 0 $ M.unions [d1,d2,d3],
      fapp = \i d1 d2 -> return $ M.insert i 0 $ M.union d1 d2,
      ffix = \i d1 -> return $ M.insert i 0 d1
      }

