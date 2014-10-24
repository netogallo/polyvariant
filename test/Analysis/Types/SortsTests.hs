module Analysis.Types.SortsTests where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Control.Applicative
import Analysis.Types.Sorts

instance Arbitrary Sort where

  arbitrary = do
    s <- elements [1..4]
    case s of
      1 -> return Eff
      2 -> return Ann
      _ -> Arr <$> arbitrary <*> arbitrary

  shrink x =
    case x of
      Eff -> []
      Ann -> []
      Arr a b -> merge a b

    where
      merge a b = [Eff,Ann,a,b] ++ [Arr x y | (x,y) <- shrink (a,b)]
