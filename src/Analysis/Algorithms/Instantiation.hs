module Analysis.Algorithms.Instantiation where

import Analysis.Types.AnnType
import Analysis.Algorithms.Common
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.State

-- | Implementation of the instantiation algorithm. This algorithm
-- removes the outer quantifiers of a type and replaces the variables
-- bound by those quantifiers with fresh free variables. It currently
-- performs one replacement per recursive call. It could be made
-- more efficient if it just simply obtained the list of all
-- replacements and then applied them in a single call to
-- replaceFree.
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
