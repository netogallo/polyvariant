module Analysis.Types.Annotation where

data Annotation =
  Var String
  | App Annotation Annotation
  deriving Show
