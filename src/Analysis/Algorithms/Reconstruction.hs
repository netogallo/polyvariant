{-# Language FlexibleContexts, MultiWayIf #-}
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

-- | Function that calculates the value of the completion alorithm
-- for every section of the LambdaCalc
calcCompletions s0 = C.foldM alg
  where
    abs i v t = do
      (tau,tau0,fv,_) <- completion (C.set v) []
      return $ completions %~ (M.insert i (tau,tau0,fv))
             $ t
    alg = (groupAlgebraInit s0){fabs=abs}

-- | Function that traverses a LambdaCalc in order to calculate the
-- value of the gamma type environment at every section of the structure
-- it also initializes the freshFlowVars field of the structure since
-- it is also necessary to initialize the environment
calcGammas s0 = C.foldM alg
  where
    app i s1 s2 = return $ gammas %~ M.insert i M.empty $ s1 C.<+> s2
    var i _ = return $ gammas %~ M.insert i M.empty $ s0
    fixF i s = return $ gammas %~ M.insert i M.empty $ s
    abs i v s = do
      b1 <- getFreshIx (ASort S.Ann)
      let Just (t1,_,_) = (M.lookup i) $ s ^. completions
      let up = M.map (M.insertWith (const id) (C.name v) (t1,b1))
      return $ gammas %~ M.insert i M.empty
             $ gammas %~ up
             $ freshFlowVars %~ M.insertWith M.union i (M.fromList [(B1,b1)])
             $ s
    alg = (groupAlgebraInit s0){fabs=abs,fvar=var,fapp=app, ffix=fixF}

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
      -- Pattern match fails if either:
      -- No variable mappings exist for this particular branch
      -- A free variable is queried which is not in the environment
      -- Neither should ever happen
      let Just (t,psi) = M.lookup v $ (\(Just x) -> x) $ M.lookup i $ s0 ^. gammas
          c = [(Left $ An.Var psi, b0), (Right $ E.Empty, d0)]
      modify (history %~ (BasicLog ((t,t),c,i,b0,d0) :))
      return (t,b0,d0,c)
    
    appF i (t1,b1,d1,c1) (t2,b2,d2,c2) = do
      (tx,_) <- inst t1
      t1'@(At.Arr (At.Ann t2' (An.Var b2')) phi' (At.Ann t' psi')) <- case At.normalize tx of
            tx'@(At.Arr (At.Ann _ (An.Var _)) _ (At.Ann _ _)) -> return tx'
            _ -> throwError $ Failure i [
              toMsg "The type ",
              toMsg tx,
              toMsg " resulting from the I algorithm",
              toMsg " does not have the expected structure ",
              toMsg (At.Arr (At.Ann (At.Var 2) (An.Var 2)) (E.Var 1) (At.Ann (At.Var 1) (An.Var 1)))]
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
      modify (history %~ (AppLog ((t,rTprime t'),c,i,b,d) (t1',tx) omega :))
      return (t,b,d,c) 

    fixF i (t1,b1,d1,c1) = do
      (tx,reps) <- inst t1
      t1'@(At.Arr (At.Ann t' b') phi0 (At.Ann t'' psi'')) <-
            case At.normalize tx of
              tx'@(At.Arr (At.Ann _ _) _ (At.Ann _ _)) -> return tx'
              _ -> throwError $ Failure i [
                toMsg "The type ",
                toMsg tx,
                toMsg " resulting from the I algorithm ",
                toMsg " does not have the expected structure."
                ]
      -- Additional replacements are calculated since the analysis results
      -- with free variables that correspond to the effects and annotations
      -- that result from the recusive calls of the fixed expression.
      -- Theese effects and annotations are recovered by collecting
      -- all expressions where the quantified variable appears in the
      -- effect and annotation signature of the functional argument
      -- of fix
      let (bRep,dRep) = case t'' of
            At.Forall v (At.Arr _ eff e) ->
              let bRep' = if S.name v `D.member` D.map fst (At.vars e)
                          then An.Abs (S.Var 1 S.Ann) (An.Var 1)
                          else An.Abs (S.Var 1 S.Ann) An.Empty
              in (bRep',E.Abs v (E.Set (E.findFlowsByExpr (An.Var (S.name v)) eff)))
            _ -> (An.Abs (S.Var 1 S.Ann) An.Empty, E.Abs (S.Var 1 S.Ann) E.Empty)
      d <- getFreshIx $ ASort $ S.Eff
      b <- getFreshIx $ ASort $ S.Ann
      omega1 <- match i M.empty t'' t'
      fvEnv <- _fvGammas <$> get
      let
        An.Var ib' = b'
        (annOmega1,_) = M.mapEither id omega1
        omega2 = M.fromList [(ib',Left $ An.replaceFree annOmega1 psi'')]
        (annOmega2,_) = M.mapEither id omega2
        cextra = map (\v ->
                       let s = (\(Just w_1919) -> w_1919) $ M.lookup v fvEnv
                       in (emptyTerm s, v)) reps
        c :: [(Either An.Annotation E.Effect, Int)]
        c = [
          (Right $ E.Var d1,d), (Right $ E.Flow (show i) (An.Var b1),d),
          (Right $ E.replaceFree omega2 $ E.replaceFree omega1 phi0, d),
          (Left $ An.replaceFree annOmega2 $ An.replaceFree annOmega1 psi'', b)
          ] ++ c1 ++ cextra
        t0 = At.replaceFree omega2 $ At.replaceFree omega1 t'
--        t' = At.normalize t0
        freeVs = D.map fst $ D.filter (not . C.bound) $ At.vars t'
        cata v o3 =
          let (ASort s) = (\(Just w_1919) -> w_1919) $ M.lookup v fvEnv
          in if | D.member v freeVs && S.annSort s -> M.insert v (Left bRep) o3
                | D.member v freeVs -> M.insert v (Right dRep) o3
                | otherwise -> o3
        omega3 = foldr cata M.empty reps
        t = At.normalize $ At.replaceFree omega3 t0
      modify (history %~ (FixLog ((t,t0),c,i,b,d) (t1',tx) omega1 omega2 :))
      return (t, b, d, c)

    boolF i = do
      b0 <- getFreshIx $ ASort S.Ann
      d0 <- getFreshIx $ ASort S.Eff
      let c = [(Left $ An.Label (show i), b0), (Right $ E.Empty, d0)]
      modify (history %~ (BasicLog ((At.TBool,At.TBool),c,i,b0,d0) :))
      return (At.TBool,b0,d0,c)

    iffF i (_,b1,d1,c1) (t2,b2,d2,c2) (t3,b3,d3,c3) = do
      fvG <- use fvGammas
      t0 <- joinTypes i t2 t3
      let t = At.normalize t0
      bSort <- case filter isJust $ map (\v -> M.lookup v fvG) [b2,b3] of
        [] -> return AnyAnnotation
        (Just s1):(Just s2):_ | s1 == s2 -> return s1
        (Just s1):[] -> return s1
        (Just s1):(Just s2):_ -> throwError $ Failure i [
          toMsg "Inconsistent sorts in the if-statement: ",
          toMsg s1,
          toMsg " and ",
          toMsg s2]
        err -> throwError $ Failure i [
          C1 "Inconsistent sorts in the if-statements ",
          C1 $ "Failed to join: " ++ show err
          ]
      updateSort b1 $ ASort S.Ann
      b0 <- getFreshIx bSort
      d0 <- getFreshIx $ ASort S.Eff
      mapM (\v -> updateSort v bSort) [b2,b3]
      let c0 = [(Right $ E.Var d1,d0),(Right $ E.Flow (show i) $ An.Var b1,d0),
            (Right $ E.Var d2,d0),(Right$ E.Var d3,d0),
            (Left $ An.Var b2,b0),(Left $ An.Var b3,b0)] ++ c1 ++ c2 ++ c3
      modify (history %~ (BasicLog ((t,t0),c0,i,b0,d0) :))
      return $ (t,b0,d0,c0)

    absF i var (t2,b2,d0,c1) = do
      let Just b1 = (M.lookup B1) . (\(Just x) -> x) . M.lookup i $ s0 ^. freshFlowVars
          (t1,t10,xis) = (\(Just x) -> x) . M.lookup i $ s0 ^. completions
          gamma = (\(Just x) -> x) . M.lookup i $ s0 ^. gammas
          ffv = map (snd . snd) $ M.toList $ M.delete (C.name var) gamma
          x = D.fromList $ [b1] ++ map S.name xis ++ ffv
          solver c x b d = solve i c x b d
      (psi1,phi0) <- solver c1 (D.toList x) b2 d0
      b0 <- getFreshIx $ ASort S.Ann
      d0 <- getFreshIx $ ASort S.Eff
      let t' = At.Arr (At.Ann t1 (An.Var b1)) phi0 (At.Ann t2 psi1)
          t0 = At.Forall (S.Var b1 S.Ann) $ foldr (\v t -> At.Forall v t) t' xis
          t = At.normalize $ t0
          c = [(Left $ An.Label $ show i,b0), (Right $ E.Empty, d0)]
          xis' = map (\v -> (S.name v, S.sort v)) xis
          x' = [(b1,S.Ann)] ++ xis' ++ map (\n -> (n,S.Ann)) ffv
      modify (history %~ (AbstLog ((t,t0),c,i,b0,d0) (t1,t10) xis' x' psi1 phi0 :))
      return (t,b0,d0,c)
      
reconstruction t = runIdentity $ flip runStateT rcontext $ runExceptT $ do
  s0 <- (initState t)
  s1 <- lift $ calcCompletions s0 t
  s2 <- calcGammas s1 t
  (t',b,d,c) <- reconstructionF s2 t
  let
    gamma = (\(Just x) -> x) . M.lookup 0 $ s2 ^. gammas
    ffv = map (snd . snd) $ M.toList gamma
  (b0,d0) <- solve 0 c ffv b d
  return (At.normalize $ At.Ann t' b0,E.normalize d0)

