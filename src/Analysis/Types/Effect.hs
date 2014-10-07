module Analysis.Types.Effect where

data Effect =
  Var String
  | App Effect Effect
  deriving Show
