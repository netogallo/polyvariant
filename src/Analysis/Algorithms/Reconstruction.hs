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

calcCompletions :: (Functor m, Monad m) => LambdaCalc T.Type -> StateT RContext m (LambdaCalc T.Type)
calcCompletions = C.foldM alg
  where
    abs i l v t = do
      res <- completion (C.set v) []
      modify (completions %~ M.insert i res)
      return $ Abs l v t
    alg = algebra{fabs=abs}

calcGammas g0 = C.foldM alg
  where
    sing i _ = modify (gammas %~ M.insert i g0)
    abs i _ v _ = do
      (t1,_) <- fromJust . (M.lookup i) . (^.completions) <$> get
      b1 <- freshAnn
      let up = M.map (M.insertWith (const id) (C.name v) (t1,b1))
      modify (annotations %~ M.insert (i,B1) b1)
      modify (gammas %~ up)
      sing i ()
    alg = Algebra{
      fvar = sing,
      fvfalse = sing,
      fvtrue = sing,
      fabs = abs,
      fif = \i _ _ _ _ -> sing i (),
      fapp = \i _ _ _ -> sing i ()
      }

reconstruction g0 t = do
  _ <- calcCompletions t
  calcGammas g0 t
  C.foldM alg t
  
  where
    abs i l var (t2,b2,d0,c1) = do
      b1 <- fromJust . M.lookup (i,B1) . (^.annotations) <$> get
      (_,comps) <- fromJust . M.lookup i . (^.completions) <$> get
      let x = D.fromList $ [b1] ++ comps
      undefined

    ifelse i l (_,t1,b1,d1,c1) (t2,b2,d2,c2) (t3,b3,d3,c3) = do
      let tau = joinTypes t2 t3
      beta <- freshAnn
      delta <- freshEff
      let c = D.unions [
            D.fromList [
               (Right $ E.Var $ S.name d1, delta),
               (Right $ E.Flow l (An.Var b1), delta),
               (Right $ E.Var $ S.name d2, delta),
               (Right $ E.Var $ S.name d3, delta),
               (Left $ An.Var $ S.name b2, beta),
               (Left $ An.Var $ S.name b3, beta)
            ],
            c1,c2,c3]
      return (tau,beta,delta,c)
      
    alg = Algebra{fabs=abs}

getContext t = undefined

