module Analysis.Algorithms.Reconstruction where

import Analysis.Algorithms.Completion
import Analysis.Algorithms.Join
import Analysis.Algorithms.Common
import qualified Analysis.Types.Common as C
import Analysis.Types.LambdaCalc
import Control.Monad.State
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import qualified Analysis.Types.Annotation as An
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Type as T
import Data.Maybe
import Control.Lens
import Control.Applicative
import qualified Data.Set as D

-- calcCompletions :: (Functor m, Monad m) => LambdaCalc T.Type -> StateT RContext m (LambdaCalc T.Type)
initState :: (Functor m, Monad m) => LambdaCalc T.Type -> m RState
initState = C.foldM alg
  where
    base i = M.insert i M.empty M.empty
    baseAll i = RState (base i) M.empty (base i) M.empty
    sing i _ = return $ baseAll i
    alg = Algebra{
      fvar = sing,
      fvfalse = sing,
      fvtrue = sing,
      fabs = \i _ _ s -> return $ baseAll i C.<+> s,
      fif = \i _ cond yes no -> return $ baseAll i C.<+> cond C.<+> yes C.<+> no,
      fapp = \i _ a1 a2 -> return $ baseAll i C.<+> a1 C.<+> a2
      }

calcCompletions :: (Functor m, Monad m) => RState -> LambdaCalc T.Type -> StateT RContext m RState
calcCompletions s0 = C.foldM alg
  where
    abs i l v t = do
      (tau,fv,freshVars) <- completion (C.set v) []
      return $ completions %~ (M.insert i (tau,fv))
             $ fvGammas %~ (\s -> foldl (\s' (n,sr) -> M.insert n (Just sr) s') s $ freshVars)
             $ t
    alg = (groupAlgebraInit s0){fabs=abs}

calcGammas s0 = C.foldM alg
  where
    abs i _ v s = do
      b1 <- getFreshIx
      let (t1,_) = fromJust . (M.lookup i) $ s ^. completions
      let up = M.map (M.insertWith (const id) (C.name v) (t1,b1))
      return $ gammas %~ up $ freshFlowVars %~ M.insertWith M.union i (M.fromList [(B1,b1)])
                            $ fvGammas %~ M.insert b1 (Just S.Ann)
                            $ s
    alg = (groupAlgebraInit s0){fabs=abs}

calcFlowGamma comps = undefined

-- flowVars s0 = C.foldM alg
  
--   where
--     varF i v = do
--       let (t,psi) = fromJust $ M.lookup v $ s0 ^. gammas
--       b0 <- getFreshIx
--       d0 <- getFreshIx
--       return $ freshFlowVars %~ M.insertWith M.union i (M.fromList [(B0,b0),(D0,d0)])
--              $ fvGammas % (M.insert b0 (Just S.Ann) . M.insert d0 Nothing) $ s0
    
--     abs i l var (t2,b2,d0,c1) = do
--       b1 <- fromJust . M.lookup (i,B1) . (^.annotations) <$> get
--       (_,comps) <- fromJust . M.lookup i . (^.completions) <$> get
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

