module Analysis.Types.SortsTests where

import Test.QuickCheck
import Control.Applicative
import Analysis.Types.Sorts
import Control.Applicative()

maxComplexity = 5

allSorts = foldl mkSorts [Ann,Eff] [1..(maxComplexity + 1)]
  where
    mkSorts s _ = s ++ concatMap (\x -> map (Arr x) s) s

instance Arbitrary Sort where

  arbitrary = (!!) allSorts <$> choose (0,maxComplexity)

  shrink x =
    case x of
      Eff -> []
      Ann -> []
      Arr a b -> merge a b

    where
      merge a b = [Eff,Ann,a,b] ++ [Arr x y | (x,y) <- shrink (a,b)]
