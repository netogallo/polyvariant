{-# Language MultiParamTypeClasses, FunctionalDependencies, RecordWildCards #-}
module Analysis.Types.LambdaCalc where
import qualified Analysis.Types.Common as C
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad.Identity

data LambdaCalc t =
  Var Int
  | VFalse String
  | VTrue String
  | Abs String (C.Variable t) (LambdaCalc t)
  | If String (LambdaCalc t) (LambdaCalc t) (LambdaCalc t)
  | App String (LambdaCalc t) (LambdaCalc t)
  deriving (Show,Read,Eq,Ord)

data Algebra t m a =
  Algebra{
    fvar :: Int -> Int -> m a,
    fvfalse :: Int -> String -> m a,
    fvtrue :: Int -> String -> m a,
    fabs :: Int -> String -> (C.Variable t) -> a -> m a,
    fif :: Int -> String -> a -> a -> a -> m a,
    fapp :: Int -> String -> a -> a -> m a
    }

algebra :: Monad m => Algebra t m (LambdaCalc t)
algebra = Algebra{
  fvar = \_ v -> return $ Var v,
  fvfalse = \_ l -> return $ VFalse l,
  fvtrue = \_ l -> return $ VTrue l,
  fabs = \_ l var s -> return $ Abs l var s,
  fif = \_ l cond yes no -> return $ If l cond yes no,
  fapp = \_ l t1 t2 -> return $ App l t1 t2
  }

instance C.LambdaCalculus (LambdaCalc t) (Algebra t) where
  lambdaDepths = depths
  byId = undefined
  foldM = foldLambdaCalcM
  app (App _ a1 a2) = Just (a1,a2)
  app _ = Nothing
  appC = undefined
  var (Var i) = Just i
  var _ = Nothing
  varC = Var
  abst (Abs _ v e) = undefined -- Just (v,e)
  abstC = undefined
  increment = undefined
  baseAlgebra = undefined


foldLambdaCalcM Algebra{..} expr = evalStateT (foldLambdaCalcM' undefined expr) 0
  where
    foldLambdaCalcM' s l = do
      i <- get
      put (i + 1)
      case l of
        Var v -> lift $ fvar i v
        VFalse lbl -> lift $ fvfalse i lbl
        VTrue lbl -> lift $ fvtrue i lbl
        Abs lbl var exp -> foldLambdaCalcM' s exp >>= lift . (fabs i lbl var)
        If lbl cond yes no -> do
          cond' <- foldLambdaCalcM' s cond
          yes' <- foldLambdaCalcM' s yes
          no' <- foldLambdaCalcM' s no
          lift $ fif i lbl cond' yes' no'
        App lbl exp1 exp2 -> do
          exp1' <- foldLambdaCalcM' s exp1
          exp2' <- foldLambdaCalcM' s exp2
          lift $ fapp i lbl exp1' exp2'

depths = runIdentity . (foldLambdaCalcM alg)
  where
    sing i _ = return $ M.fromList [(i,0 :: Int)]
    alg = Algebra{
      fvar = sing,
      fvfalse = sing,
      fvtrue = sing,
      fabs = \i _ _ d -> return $ M.insert i 0 $ M.map (+1) d,
      fif = \i _ d1 d2 d3 -> return $ M.insert i 0 $ M.unions [d1,d2,d3],
      fapp = \i _ d1 d2 -> return $ M.insert i 0 $ M.union d1 d2
      }

