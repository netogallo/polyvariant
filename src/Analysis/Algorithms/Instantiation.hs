module Analysis.Algorithms.Instantiation where

import Analysis.Types.AnnType
import Analysis.Algorithms.Common
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.State

inst' t =
  case t of
    Forall v t1 -> do
      v' <- lift $ getFreshIx $ ASort $ S.sort v
      let rep = if S.annSort $ S.sort v
                then Left (A.Var v')
                else Right (E.Var v')
      modify (v':)
      replaceFree (M.fromList [(S.name v,rep)]) <$> inst' t1
    t -> return t
        
inst t = runStateT (inst' t) []
