module Analysis.Examples where

import Analysis.Types.LambdaCalc
import Analysis.Types.Type
import qualified Analysis.Types.Common as C

t0 = Abs (C.Var 1 TBool) (If (Var 1) VFalse VTrue)

t1 = Abs (C.Var 1 TBool) (If (Var 1) VTrue (Var 1))

t2 = Abs (C.Var 1 (Arr TBool TBool)) (
  If VTrue
  (Var 1)
  (Abs (C.Var 2 TBool) (Var 2)))

t3 = Abs (C.Var 1 (Arr TBool TBool)) (
  If (App (Var 1) VTrue)
  VFalse
  VTrue)

t4 = Abs (C.Var 1 (Arr (Arr TBool TBool) TBool)) (If (App (Var 1) (Abs (C.Var 2 TBool) VTrue)) VFalse VTrue)

t5 = Fix (Abs (C.Var 1 (Arr TBool TBool)) (Abs (C.Var 2 TBool) (If (Var 2) (App (Var 1) VFalse) VTrue)))

t6 = App t5 VTrue

t7 = App t3 t0

t8 = App t4 (Abs (C.Var 2 (Arr TBool TBool)) (App (Var 2) VFalse))

t9 = Fix (Abs (C.Var 1 (Arr TBool TBool)) (Var 1))

t10 = Fix (Abs (C.Var 1 (Arr TBool (Arr TBool TBool))) (Abs (C.Var 2 TBool) (Abs (C.Var 3 TBool) (If (Var 2) (App (App (Var 1) VFalse) VFalse) (Var 3)))))

t11 = App (App t10 VTrue) VFalse

t12 = Fix (Abs (C.Var 1 (Arr TBool (Arr TBool TBool))) (Abs (C.Var 2 TBool) (If (Var 2) (Abs (C.Var 3 TBool) (If (Var 2) (App (App (Var 1) VFalse) VFalse) (Var 3))) (Abs (C.Var 3 TBool) (Var 3)))))

t13 = App (App t12 VTrue) VFalse

allExamples = [t0,t1,t2,t3,t7,t4,t8,t5,t6,t9,t10,t11]
