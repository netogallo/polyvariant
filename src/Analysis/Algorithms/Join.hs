module Analysis.Algorithms.Join where
import Analysis.Types.AnnType
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as An
import Control.Monad.Identity
import Control.Monad.Except
import Analysis.Algorithms.Common

-- | This is an (line by line) implementation of the J algorithm described by the analysis.
-- It requires that both t1' and t2' arguments are normalized. Otherwise the
-- alorithm might fail in cases where both types should be joinable. Thanks to the
-- normalization of types, the algorithm can be implemented in a very clean
-- fashion.
joinTypes l t1' t2' = joinE t1' t2'
  where
    joinE t1 t2 =
      case (t1,t2) of
        (Arr (Ann t1' b1@(An.Var i)) eff1 (Ann t1'' a1), Arr (Ann t2' (An.Var j)) eff2 (Ann t2'' a2)) | i == j && t1' == t2' -> do
          res <- joinE t1'' t2''
          return $ Arr (Ann t1' b1) (E.Union eff1 eff2) (Ann res (An.Union a1 a2))
        (Forall var1 t1',Forall var2 t2') | var1 == var2 -> do
          res <- joinE t1' t2'
          return $ Forall var1 res
        (TBool, TBool) -> return TBool
        _ -> throwError $ Failure l [
          C1 "Could not join types: ",
          C4 t1, C1 " and ", C4 t2]
