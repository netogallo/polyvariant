module Analysis.Algorithms.Completion where
import qualified Analysis.Types.AnnType as A
import qualified Analysis.Types.Type as T
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as An
import Analysis.Algorithms.Common
import Control.Monad.State
import Control.Applicative
import Control.Lens
import qualified Data.Map as M
  
completion' :: (Monad m, Functor m) =>
               ((A.Type, [S.FlowVariable], [(Int,S.Sort)]) -> StateT RContext m (A.Type, [S.FlowVariable], [(Int,S.Sort)]))
               -> T.Type
               -> [S.FlowVariable]
               -> StateT RContext m (A.Type, [S.FlowVariable], [(Int,S.Sort)])
completion' cont T.TBool _ = cont (A.TBool, [], [])
completion' cont (T.Arr t1 t2) c0 = completion' cont' t1 [] >>= cont
  where
    mkVar v = do
      -- Pattern match failure ocurrs if an inexistent variable
      -- is looked up in the environment. The implementation
      -- of the algorithm should not allow this to happen
      s <- (\(Just x) -> x) . M.lookup v <$> use fvGammas
      if isAnnConstraint s
        then return $ Left $ An.Var v
        else return $ Right $ E.Var v
    appEff e arg =
      case arg of
        Left ann -> E.AppAnn e ann
        Right eff -> E.App e eff
    cont'' b1 (tau1,c1,freshVars1) (tau2,c2,freshVars2) = do
      b0 <- getFreshIx AnyAnnotation
      d0 <- getFreshIx AnyEffect
      let
        ffvs = map S.name $ c0 ++ [b1] ++ c1
      eff <- foldl appEff (E.Var d0) <$> mapM mkVar ffvs
      let
        bi' = filter (S.annSort . S.sort) c0
        bj' = filter (S.annSort . S.sort) c1
        annvs = bi' ++ [b1] ++ bj'
        ann = foldl An.App (An.Var b0) $ map (An.Var . S.name) annvs
        tau' = A.Arr (A.Ann tau1 (An.Var $ S.name b1)) eff (A.Ann tau2 ann)
        tau = foldr (\v t -> (A.Forall v t)) tau' $ b1:c1
        sd0 =
          let
            ss = map S.sort c0 ++ [S.Ann] ++ map S.sort c1 ++ [S.Eff]
          in foldr1 S.Arr ss
        sb0 =
          let
            ss = map S.sort bi' ++ [S.Ann] ++ map S.sort bj' ++ [S.Ann]
          in foldr1 S.Arr ss
      updateSort d0 $ ASort sd0
      updateSort b0 $ ASort sb0
      return (tau, [S.Var d0 sd0, S.Var b0 sb0] ++ c2, (d0,sd0):(b0,sb0):freshVars1 ++ freshVars2)
    
    cont' (tau1, c1, freshVars) = do
      b1 <- flip S.Var S.Ann <$> getFreshIx (ASort S.Ann)
      completion' (cont'' b1 (tau1,c1, (S.name b1,S.Ann) : freshVars)) t2 (c0 ++ [b1] ++ c1)

completion :: (Monad m, Functor m) =>
              T.Type
              -> [S.FlowVariable]
              -> StateT RContext m (A.Type, [S.FlowVariable], [(Int,S.Sort)])
completion ty fv = do
  (t,ss,freshVars) <- completion' return ty fv
  return (A.normalize t,ss,freshVars)
