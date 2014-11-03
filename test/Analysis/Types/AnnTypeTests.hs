{-# Language MultiWayIf #-}
module Analysis.Types.AnnTypeTests where

import Test.QuickCheck
import Test.QuickCheck.Gen
import Analysis.Types.AnnType
import qualified Analysis.Types.AnnotationTests as AT
import qualified Analysis.Types.EffectTests as ET
import qualified Analysis.Types.Sorts as S
import Control.Applicative
import qualified Data.Map as M

arbitraryWithGamma gamma = do
  let var = choose (1,3) :: Gen Int
  p <- choose (0,99) :: Gen Int
  if | p `mod` 5 < 2 -> return TBool
     | p `mod` 5 < 3 -> 
         Ann <$> arbitraryWithGamma gamma 
             <*> AT.arbitraryWithGammaAndSort gamma S.Ann
     | p `mod` 5 < 4 -> do
         v <- var
         s <- arbitrary
         Forall (S.Var v s) <$> (arbitraryWithGamma $ M.insert v s gamma)
     | otherwise -> 
         Arr <$> arbitraryWithGamma gamma 
             <*> ET.arbitraryWithGammaAndSort gamma S.Eff
             <*> arbitraryWithGamma gamma

instance Arbitrary Type where
  arbitrary = arbitraryWithGamma M.empty
  shrink = const []
         

    
