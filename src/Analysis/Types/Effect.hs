module Analysis.Types.Effect where

data Effect =
  Var Int
  | App Effect Effect
  deriving Show
