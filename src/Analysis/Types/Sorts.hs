module Analysis.Types.Sorts where

data Sort =
  Ann
  | Eff
  | Arr Sort Sort
  deriving (Show,Eq,Ord,Read)

data FlowVariable =
  Var {name :: Int, sort :: Sort}
  deriving (Show,Ord,Eq,Read)

isAnn Ann = True
isAnn _ = False
