module Analysis.Types.Sorts where
import Control.Lens

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

annSort :: Sort -> Bool
annSort Ann = True
annSort (Arr s1 s2) = annSort s1 && annSort s2
annSort _ = False

effSort :: Sort -> Bool
effSort = not . annSort
