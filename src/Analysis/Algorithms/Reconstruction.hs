{-# Language FlexibleContexts #-}
module Analysis.Algorithms.Reconstruction where

import Analysis.Algorithms.Completion
import Analysis.Algorithms.Join
import Analysis.Algorithms.Common
import Analysis.Algorithms.Solve
import Analysis.Algorithms.Instantiation
import Analysis.Algorithms.Match
import qualified Analysis.Types.Common as C
import Analysis.Types.LambdaCalc
import Control.Monad.State
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import qualified Analysis.Types.Annotation as An
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Type as T
import qualified Analysis.Types.AnnType as At
import Data.Maybe
import Control.Lens
import Control.Applicative
import qualified Data.Set as D
import Control.Monad.Except

-- calcCompletions :: (Functor m, Monad m) => LambdaCalc T.Type -> StateT RContext m (LambdaCalc T.Type)
initState :: (Functor m, Monad m) => LambdaCalc T.Type -> m RState
initState = C.foldM alg
  where
    base i = M.insert i M.empty M.empty
    baseAll i = RState (base i) M.empty M.empty
    sing i = return $ baseAll i
    alg = Algebra{
      fvar = \i _ -> sing i,
      fvfalse = sing,
      fvtrue = sing,
      fabs = \i _ s -> return $ baseAll i C.<+> s,
      fif = \i cond yes no -> return $ baseAll i C.<+> cond C.<+> yes C.<+> no,
      fapp = \i a1 a2 -> return $ baseAll i C.<+> a1 C.<+> a2,
      ffix = \i s -> return $ baseAll i C.<+> s
      }

-- calcCompletions :: (Functor m, Monad m) => RState -> LambdaCalc T.Type -> StateT RContext m RState
calcCompletions s0 = C.foldM alg
  where
    abs i v t = do
      (tau,fv,_) <- completion (C.set v) []
      return $ completions %~ (M.insert i (tau,fv))
             $ t
    alg = (groupAlgebraInit s0){fabs=abs}

calcGammas s0 = C.foldM alg
  where
    var i _ = return $ gammas %~ M.insert i M.empty $ s0
    abs i v s = do
      b1 <- getFreshIx (ASort S.Ann)
      let Just (t1,_) = (M.lookup i) $ s ^. completions
      let up = M.map (M.insertWith (const id) (C.name v) (t1,b1))
      return $ gammas %~ M.insert i M.empty
             $ gammas %~ up
             $ freshFlowVars %~ M.insertWith M.union i (M.fromList [(B1,b1)])
             $ s
    alg = (groupAlgebraInit s0){fabs=abs,fvar=var}          

reconstructionF :: (MonadError RFailure m, MonadState RContext m, C.Fold a (Algebra T.Type), Functor m, Monad m, Applicative m) =>
                   RState -> a -> m (At.Type, Int, Int, [(Either An.Annotation E.Effect, Int)])
reconstructionF s0 = C.foldM alg
  
  where
    alg = Algebra{
      fvfalse = boolF,
      fvtrue = boolF,
      fvar = varF,
      fif = iffF,
      fapp = appF,
      ffix = fixF,
      fabs = absF}
    varF i v = do
      -- The constraint {} c d0 is added artificially so the
      -- constraint solving algorithm is easier to implement
      b0 <- getFreshIx (ASort S.Ann)
      d0 <- getFreshIx $ ASort S.Eff
      let Just (t,psi) = M.lookup v $ (\(Just x) -> x) $ M.lookup i $ s0 ^. gammas
          c = [(Left $ An.Var psi, b0), (Right $ E.Empty, d0)]
      modify (history %~ (BasicLog (t,c,i,b0,d0) :))
      return (t,b0,d0,c)
    
    appF i (t1,b1,d1,c1) (t2,b2,d2,c2) = do
      t1'@(At.Arr (At.Ann t2' (An.Var b2')) phi' (At.Ann t' psi')) <- At.normalize <$> inst t1
      d <- getFreshIx $ ASort $ S.Eff
      b <- getFreshIx $ ASort $ S.Ann
      omega <- M.insert b2' (Left $ An.Var b2) <$> match i M.empty t2 t2'
      let
          (annOmega,_) = M.mapEither id omega
          c = [
            (Right $ E.Var d1,d),(Right $ E.Var d2,d),(Right $ E.Flow (show i) (An.Var b1),d),
            (Right $ rPhi phi',d),
            (Left $  rPsi psi', b)
            ] ++ c1 ++ c2
          rPhi phi = E.replaceFree omega phi
          rPsi psi = An.replaceFree annOmega psi
          rTprime ty = At.replaceFree omega ty
          t = At.normalize $ rTprime t'
      modify (history %~ (AppLog (t,c,i,b,d) t1' omega :))
      return (t,b,d,c) 

    fixF i (t1,b1,d1,c1) = do
      t1'@(At.Arr (At.Ann t' b') phi0 (At.Ann t'' psi'')) <- At.normalize <$> inst t1
      d <- getFreshIx $ ASort $ S.Eff
      b <- getFreshIx $ ASort $ S.Ann
      omega1 <- match i M.empty t'' t'
      let
          (annOmega1,_) = M.mapEither id omega1
          omega2 = M.fromList [(b1,Left $ An.replaceFree annOmega1 psi'')]
          (annOmega2,_) = M.mapEither id omega2
          c :: [(Either An.Annotation E.Effect, Int)]
          c = [
            (Right $ E.Var d1,d), (Right $ E.Flow (show i) (An.Var b1),d),
            (Right $ E.replaceFree omega2 $ E.replaceFree omega1 phi0, d),
            (Left $ An.replaceFree annOmega2 $ An.replaceFree annOmega1 psi'', b)
            ] ++ c1
          t = At.replaceFree omega2 $ At.replaceFree omega1 t'
      modify (history %~ (FixLog (t,c,i,b,d) t1' omega1 omega2 :))
      return (t, b, d, c)

    boolF i = do
      b0 <- getFreshIx $ ASort S.Ann
      d0 <- getFreshIx $ ASort S.Eff
      let c = [(Left $ An.Label (show i), b0), (Right $ E.Empty, d0)]
      modify (history %~ (BasicLog (At.TBool,c,i,b0,d0) :))
      return (At.TBool,b0,d0,c)

    iffF i (_,b1,d1,c1) (t2,b2,d2,c2) (t3,b3,d3,c3) = do
      fvG <- use fvGammas
      let t = At.normalize $ joinTypes t2 t3
          bSort = case filter isJust $ map (\v -> M.lookup v fvG) [b2,b3] of
            [] -> AnyAnnotation
            (Just s1):(Just s2):_ | s1 == s2 -> s1
            (Just s1):[] -> s1
            s1:s2:_ -> error $ "Inconsistent sorts: " ++ show s1 ++ " and " ++ show s2
      updateSort b1 $ ASort S.Ann
      b0 <- getFreshIx bSort
      d0 <- getFreshIx $ ASort S.Eff
      mapM (\v -> updateSort v bSort) [b2,b3]
      let c0 = [(Right $ E.Var d1,d0),(Right $ E.Flow (show i) $ An.Var b1,d0),
            (Right $ E.Var d2,d0),(Right$ E.Var d3,d0),
            (Left $ An.Var b2,b0),(Left $ An.Var b3,b0)] ++ c1 ++ c2 ++ c3
      modify (history %~ (BasicLog (t,c0,i,b0,d0) :))
      return $ (t,b0,d0,c0)

--    absF :: (Functor m, Monad m) => Int -> (C.Variable T.Type) -> (At.Type,Int,Int,[(Either An.Annotation E.Effect,Int)]) -> StateT RContext m (At.Type,Int,Int,[(Either An.Annotation E.Effect,Int)])
    absF i var (t2,b2,d0,c1) = do
      let Just b1 = (M.lookup B1) . (\(Just x) -> x) . M.lookup i $ s0 ^. freshFlowVars
          (t1,xis) = (\(Just x) -> x) . M.lookup i $ s0 ^. completions
          gamma = (\(Just x) -> x) . M.lookup i $ s0 ^. gammas
          ffv = map (snd . snd) $ M.toList $ M.delete (C.name var) gamma
          x = D.fromList $ [b1] ++ map S.name xis ++ ffv
          solver c x b d = solve c x b d
      (psi1,phi0) <- solver c1 (D.toList x) b2 d0
      b0 <- getFreshIx $ ASort S.Ann
      d0 <- getFreshIx $ ASort S.Eff
      let t' = At.Arr (At.Ann t1 (An.Var b1)) phi0 (At.Ann t2 psi1)
          t = At.normalize $ At.Forall (S.Var b1 S.Ann) $ foldr (\v t -> At.Forall v t) t' xis
          c = [(Left $ An.Label $ show i,b0), (Right $ E.Empty, d0)]
          xis' = map (\v -> (S.name v, S.sort v)) xis
          x' = [(b1,S.Ann)] ++ xis' ++ map (\n -> (n,S.Ann)) ffv
      modify (history %~ (AbstLog (t,c,i,b0,d0) t1 xis' x' psi1 phi0 :))
      return (t,b0,d0,c)
      
reconstruction t = runIdentity $ flip runStateT rcontext $ runExceptT $ do
  s0 <- (initState t)
  s1 <- lift $ calcCompletions s0 t
  s2 <- calcGammas s1 t
  reconstructionF s2 t
  

--     abs i l var (t2,b2,d0,c1) = do
--       b1 <- fromJust . M.lookup (i,B1) . (^.annotations) <$> get
--       (_,comps) <- (\(Just x) -> x) . M.lookup i . (^.completions) <$> get
--       let x = D.fromList $ [b1] ++ comps
--       undefined

--     ifelse i l (_,t1,b1,d1,c1) (t2,b2,d2,c2) (t3,b3,d3,c3) = do
--       let tau = joinTypes t2 t3
--       beta <- freshAnn
--       delta <- freshEff
--       let c = D.unions [
--             D.fromList [
--                (Right $ E.Var $ S.name d1, delta),
--                (Right $ E.Flow l (An.Var b1), delta),
--                (Right $ E.Var $ S.name d2, delta),
--                (Right $ E.Var $ S.name d3, delta),
--                (Left $ An.Var $ S.name b2, beta),
--                (Left $ An.Var $ S.name b3, beta)
--             ],
--             c1,c2,c3]
--       return (tau,beta,delta,c)
      
--     alg = Algebra{fabs=abs}

-- getContext t = undefined

