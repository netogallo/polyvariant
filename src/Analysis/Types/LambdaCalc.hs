{-# Language MultiParamTypeClasses, FunctionalDependencies, RecordWildCards, FlexibleContexts #-}
module Analysis.Types.LambdaCalc where
import qualified Analysis.Types.Common as C
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad.Identity
import qualified Analysis.Types.Sorts as S
import Control.Monad.Except
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as A

data LambdaCalc t =
  Var Int
  | VFalse
  | VTrue
  | Abs (C.Variable t) (LambdaCalc t)
  | If (LambdaCalc t) (LambdaCalc t) (LambdaCalc t)
  | App (LambdaCalc t) (LambdaCalc t)
  | Fix (LambdaCalc t)
  deriving (Show,Read,Eq,Ord)

data ALambdaCalc t =
  AVar Int Int
  | AFalse Int
  | ATrue Int
  | AAbs Int (C.Variable t) (ALambdaCalc t)
  | AIf Int (ALambdaCalc t) (ALambdaCalc t) (ALambdaCalc t)
  | AApp Int (ALambdaCalc t) (ALambdaCalc t)
  | AFix Int (ALambdaCalc t)
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

aalgebra :: Monad m => Algebra t m (ALambdaCalc t) (ALambdaCalc t)
aalgebra = Algebra{
  fvar = \i v -> return $ AVar i v,
  fvfalse = \i -> return $ AFalse i,
  fvtrue = \i -> return $ ATrue i,
  fabs = \i var s -> return $ AAbs i var s,
  fif = \i cond yes no -> return $ AIf i cond yes no,
  fapp = \i t1 t2 -> return $ AApp i t1 t2,
  ffix = \i t1 -> return $ AFix i t1
  }

instance C.Fold (ALambdaCalc t) (Algebra t) where
  byId = undefined
  foldM = foldALambdaCalcM
  baseAlgebra = aalgebra
  groupAlgebra = groupAlgebraInit C.void

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

foldALambdaCalcM Algebra{..} expr = foldLambdaCalcM' undefined expr
  where
    foldLambdaCalcM' s l = do
      case l of
        AVar i v -> fvar i v
        AFalse i -> fvfalse i
        ATrue i -> fvtrue i
        AAbs i var exp -> foldLambdaCalcM' s exp >>= fabs i var
        AIf i cond yes no -> do
          cond' <- foldLambdaCalcM' s cond
          yes' <- foldLambdaCalcM' s yes
          no' <- foldLambdaCalcM' s no
          fif i cond' yes' no'
        AApp i exp1 exp2 -> do
          exp1' <- foldLambdaCalcM' s exp1
          exp2' <- foldLambdaCalcM' s exp2
          fapp i exp1' exp2'
        AFix i exp -> foldLambdaCalcM' s exp >>= ffix i

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

addLabels = runIdentity . (foldLambdaCalcM alg)
  where
    varF i v = return $ AVar i v
    falseF i = return $ AFalse i
    trueF i = return $ ATrue i
    absF i v e = return $ AAbs i v e
    ifF i cond yes no = return $ AIf i cond yes no
    appF i a1 a2 = return $ AApp i a1 a2
    fixF i a = return $ AFix i a
    alg = Algebra{
      fvar = varF,
      fvfalse = falseF,
      fvtrue = trueF,
      fabs = absF,
      fif = ifF,
      fapp = appF,
      ffix = fixF
      }

shadows v = runIdentity . (foldALambdaCalcM alg)
  where
    varF i _ = return $ M.fromList [(i,False)]
    falseF i = return $ M.fromList [(i,False)]
    trueF i = return $ M.fromList [(i,False)]
    absF i v' s =
      let s' = if C.name v' == v
               then M.map (const True) s
               else s
      in return $ M.insert i False s'
    ifF i cond yes no = return $ M.insert i False $ cond `M.union` yes `M.union` no
    appF i a1 a2 = return $ M.insert i False $ M.union a1 a2
    fixF i a = return $ M.insert i False a
    alg = Algebra{
      fvar = varF,
      fvfalse = falseF,
      fvtrue = trueF,
      fabs = absF,
      fif = ifF,
      fapp = appF,
      ffix = fixF
      }

replace v e e1 = snd $ runIdentity $ (foldALambdaCalcM alg e)
  where
    falseF i = return (AFalse i,AFalse i)
    trueF i = return (ATrue i,ATrue i)
    varF i v'
      | v' == v = return $ (AVar i v',e1)
      | otherwise = return $ (AVar i v',AVar i v')
    absF i v' (ex1,ex2)
      | v == C.name v' = let r = AAbs i v' ex1 in return (r,r)
      | otherwise = return (AAbs i v' ex1, AAbs i v' ex2)
    ifF i (cond1,cond2) (yes1,yes2) (no1,no2) =
      return (
        AIf i cond1 yes1 no1,
        AIf i cond2 yes2 no2)
    appF i (f1,f2) (a1,a2) = return  (AApp i f1 a1,AApp i f2 a2)
    fixF i (fix1,fix2) = return (AFix i fix1,AFix i fix2)
    alg = Algebra{
      fvfalse = falseF,
      fvtrue = trueF,
      fabs = absF,
      fif = ifF,
      ffix = fixF,
      fapp = appF,
      fvar = varF}

reduce whnf e = (reduceStep whnf e) >>= go e
  where
    go e1 (e2,effs)
      | e1 == e2 = return (e2,effs)
      | otherwise = do
        (e2',effs') <- reduceStep whnf e2
        go e2 (e2',effs ++ effs')

reduceStep whnf c =
  case c of
    AApp i e1@(AFix _ _) e2 ->
      if whnf then return (AApp i e1 e2,[]) else doApp i e1 e2
    AApp i e1 e2 -> doApp i e1 e2
    AIf i cond yes no -> do
      (cond',eff1) <- reduce whnf cond
      case cond' of
        ATrue i' -> do
          (yes',eff2) <- reduce whnf yes
          return $ (yes',eff1 ++ [E.Flow (show i) (A.Label (show i'))] ++ eff2)
        AFalse i' -> do
          (no',eff3) <- reduce whnf no
          return $ (no',eff1 ++ [E.Flow (show i) (A.Label (show i'))] ++ eff3)
        _ -> throwError $ "Cannot reduce: " ++ show c
    (AFix i e) -> do
      (e',effs1) <- reduce whnf e
      case e' of
        (AAbs i' v ex) -> do
          (e'',effs2) <- reduce True $ replace (C.name v) ex (AFix i e)
          return (e'',effs1 ++ [E.Flow (show i) (A.Label (show i'))] ++ effs2)
        _ -> throwError $ "Cannot reduce: " ++ show c
    e -> return (e,[])
  where
    doApp i e1 e2 = do
      (e1',effs1) <- reduce whnf e1
      (e2',effs2) <- reduce whnf e2
      case e1' of
        (AAbs i' v e) -> do
          (e3,effs3) <- reduce whnf $ replace (C.name v) e e2'
          return (e3, (E.Flow (show i) (A.Label (show i'))) : effs1 ++ effs2 ++ effs3)
        _ -> throwError $ "Cannot reduce: " ++ show c
  

reduceExpr :: (Show t,Eq t) => LambdaCalc t -> Either String (ALambdaCalc t,[E.Effect])
reduceExpr = runExcept . reduce False . addLabels
