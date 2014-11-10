module Analysis.Examples where

import Analysis.Types.LambdaCalc
import Analysis.Types.Type
import qualified Analysis.Types.Common as C


t1 = Abs (C.Var 1 (Arr TBool TBool)) (
  If VTrue
  (Var 1)
  (Abs (C.Var 2 TBool) (Var 2)))
