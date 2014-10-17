module Analysis.Types.Sorts where

data Sort =
  Ann
  | Eff
  | Arr Sort Sort
  deriving (Show,Eq,Ord)

data FlowVariable =
  Var {name :: Int, sort :: Sort}
  deriving (Show, Ord, Eq)

isAnn Ann = True
isAnn _ = False
