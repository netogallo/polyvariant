module Analysis.Examples where

import Analysis.Types.LambdaCalc
import Analysis.Types.Type
import qualified Analysis.Types.Common as C

t0 = Abs (C.Var 1 TBool) (If (Var 1) VTrue VFalse)

t1 = Abs (C.Var 1 TBool) (If (Var 1) VTrue (Var 1))

t2 = Abs (C.Var 1 (Arr TBool TBool)) (
  If VTrue
  (Var 1)
  (Abs (C.Var 2 TBool) (Var 2)))

t3 = Abs (C.Var 1 (Arr TBool TBool)) (
  If (App (Var 1) VTrue)
  VFalse
  VTrue)

allExamples = [t0,t1,t2,t3]
