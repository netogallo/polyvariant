module Analysis.Algorithms.Completion where
import Analysis.Types.AnnType
import qualified Analysis.Types.Type as T
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as An
import Control.Applicative

join t1 t2 = 
  case (t1,t2) of
    (Arr (Ann t1' (An.Var i)) eff1 (Ann t1'' a1), Arr (Ann t2' (An.Var j)) eff2 (Ann t2'' a2)) ->
      undefined
    
