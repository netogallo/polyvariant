module Analysis.Types.AnnType where
import Analysis.Types.Effect
import Analysis.Types.Annotation
import Analysis.Types.Sorts

data Type =
  TBool
  | Arr Type Effect Type
  | Ann Type Annotation
  | Forall FlowVariable Type
  deriving Show
