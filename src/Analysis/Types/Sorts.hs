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

-- | Represents the `simplified kind` of a sort
-- by this it is meant only to count the number
-- of abstractions at rank 0.
-- for example:
-- Eff -> (Eff -> Eff) -> Eff = 3
-- Ann -> Ann = 2
type SimpleKind = Int

isAnn Ann = True
isAnn _ = False

annSort :: Sort -> Bool
annSort Ann = True
annSort (Arr s1 s2) = annSort s1 && annSort s2
annSort _ = False

effSort :: Sort -> Bool
effSort = not . annSort

simpleKind (Arr _ b) = 1 + simpleKind b
simpleKind _ = 1
