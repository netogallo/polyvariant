import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Analysis.Types.Tests

main :: IO ()
main = defaultMain tests

tests :: [TF.Test]
tests = [
  testGroup "QuickCheck - Normalize" [
     testProperty "Normal forms of equal effects are equal" effNormalizeEquivalent,
     testProperty "Normal forms of equal annotations are equal" annNormalizeEquivalent
  ],
  testGroup "QuickCheck - Union reductions" [
    testProperty "Abstractions over the same variable to a union get united" effRedUnionEq
    ]
  ]
     
