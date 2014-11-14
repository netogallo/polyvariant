module Analysis.Types.Type where

data Type =
  TBool
  | Arr Type Type
  deriving (Show,Read)
