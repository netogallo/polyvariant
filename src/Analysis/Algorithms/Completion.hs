module Analysis.Algorithms.Completion where
import qualified Analysis.Types.AnnType as A
import qualified Analysis.Types.Type as T
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as An
import Control.Monad.State
import Control.Applicative

fresh :: Monad m => StateT Int m (S.Sort -> S.FlowVariable)
fresh = do
  v <- get
  put (v + 1)
  return $ S.Var v

freshAnn :: (Monad m, Functor m) => StateT Int m S.FlowVariable
freshAnn = (\f -> f S.Ann) <$> fresh

freshEff :: (Monad m, Functor m) => StateT Int m S.FlowVariable
freshEff = (\f -> f S.Eff) <$> fresh

completion' :: (Monad m, Functor m) =>
               ((A.Type, [S.FlowVariable]) -> StateT Int m (A.Type, [S.FlowVariable]))
               -> T.Type
               -> [S.FlowVariable]
               -> StateT Int m (A.Type, [S.FlowVariable])
completion' cont T.TBool _ = cont (A.TBool, [])
completion' cont (T.Arr t1 t2) c0 = completion' cont' t1 [] >>= cont
  where
    cont'' b1 (tau1,c1) (tau2,c2) = do
      b0 <- freshAnn
      d0 <- freshEff
      let
        ffvs = map S.name $ c0 ++ [b1] ++ c1
        eff = foldl E.App (E.Var $ S.name d0) $ map E.Var ffvs
        bi' = filter (S.isAnn . S.sort) c0
        bj' = filter (S.isAnn . S.sort) c1
        annvs = bi' ++ [b1] ++ bj'
        ann = foldl An.App (An.Var (S.name b0)) $ map (An.Var . S.name) annvs
        tau' = foldl (\s v -> \t -> s (A.Forall v t)) (A.Forall b1) c1
        tau = tau' $ A.Arr (A.Ann tau1 (An.Var $ S.name b1)) eff (A.Ann tau2 ann)
        sd0 =
          let
            ss = map S.sort c0 ++ [S.Ann] ++ map S.sort c1 ++ [S.Eff]
          in foldr1 S.Arr ss
        sb0 =
          let
            ss = map S.sort bi' ++ [S.Ann] ++ map S.sort bj' ++ [S.Ann]
          in foldr1 S.Arr ss
      return (tau, [d0{S.sort=sd0}, b0{S.sort=sb0}] ++ c2)
    
    cont' (tau1, c1) = do
      b1 <- freshAnn
      completion' (cont'' b1 (tau1,c1)) t2 (c0 ++ [b1] ++ c1)

completion :: (Monad m, Functor m) =>
              T.Type
              -> [S.FlowVariable]
              -> StateT Int m (A.Type, [S.FlowVariable])
completion = completion' return
