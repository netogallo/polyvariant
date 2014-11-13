module Analysis.Algorithms.Instantiation where

import Analysis.Types.AnnType
import Analysis.Algorithms.Common
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Data.Map as M
import Control.Applicative

inst t =
  case t of
    Forall v t1 -> do
      v' <- getFreshIx $ ASort $ S.sort v
      let rep = if S.annSort $ S.sort v
                then Left (A.Var v')
                else Right (E.Var v')
      replaceFree (M.fromList [(S.name v,rep)]) <$> inst t1
    t -> return t
        
