module Analysis.Types.Sorts where

data Sort =
  Ann
  | Eff
  | Arr Sort Sort
  deriving Show

data FlowVariable =
  Var {name :: String, sort :: Sort}
  deriving Show

isAnn Ann = True
isAnn _ = False
