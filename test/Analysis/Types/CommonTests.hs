{-# Language ViewPatterns #-}
module Analysis.Types.CommonTests where

import Test.QuickCheck
import Analysis.Types.Common
import qualified Data.Set as D
import qualified Control.Monad as M
import Control.Applicative
import Control.Monad.State hiding (foldM)
import qualified Data.Map as Ma
import Control.Monad.Identity (runIdentity)

maxTermSize = 20
 
(\\) (_:xs) 0 = xs
(\\) (x:xs) i = x : xs \\ (i-1)

-- | Helper function to shuffle a list in the Gen monad
shuffle :: [a] -> Gen [a]
shuffle s'@(_:_) = snd <$> (M.foldM cata (s',[]) $ replicate (length s') ())
  where
    cata (s,e) _ = do
      i <- choose (0,length s - 1)
      return (s \\ i,s !! i : e)
shuffle [] = return []

-- | Re-write rule that changes the order of
-- elements in Set elements (ie. elements connected via
-- nested applications of the union constructor)
asocEq :: (Fold a alg, WithSets a alg, Ord a) => a -> Gen a
asocEq (unionM -> Just (x,y)) = do
  let Just s = setM $ unions $ unionC x y
  foldl unionC emptyC <$> (shuffle $ D.toList s)
asocEq x = return x

-- | Re-write rule that applies the union
-- of a set to an empty set. It is required
-- that a set united with the empty set
-- is equal to the original set
emptyEq (unionM -> Just (x,y)) = do
  which <- arbitrary
  return $ if which
           then unionC x $ unionC y emptyC
           else unionC (unionC x emptyC) y
emptyEq a = return a

-- | Re-write rule that applies the union
-- constructor to the same set. The union
-- of a set with itself is the same set
identEq e = do
  which <- arbitrary
  return $ case e of
    (unionM -> Just (a,b)) | which -> unionC a $ unionC a b
    (unionM -> Just (a,b)) -> unionC (unionC a b) b
    (emptyM -> Just _) -> unionC emptyC emptyC
    _ -> e

-- | Helper function that applies a re-write
-- rule with probability p
maybeRuleProb p r s = do
  apply <- choose p
  if apply < (1 :: Int)
    then r s
    else return s

-- | Re-write rule that applies one or more of the
-- set re-write rules with probability p
unionEq p =
  maybeRuleProb (0,p) asocEq M.>=>
  maybeRuleProb (0,p) identEq M.>=>
  maybeRuleProb (0,p) emptyEq

-- | Search within a structure if there exists an element that can be abstracted away.
-- Return the abstracted element (if any) and a new structure with the extracted element
-- replaced by the variable provided as input. The selection is done randomly.
randomReplaceAlg :: (LambdaCalculus a alg, WithSets a alg, Ord a) => Int -> alg (StateT (Maybe a) Gen) a a
randomReplaceAlg v = alg
  where
    ifReplaced yes no = do
      r <- get
      case r of
        Nothing -> no
        Just _ -> yes
    maybeReplace elem = do
      let
        canReplace = D.isSubsetOf (D.filter (not . bound) $ vars elem) D.empty
      r <- lift arbitrary
      case r of
        True | canReplace -> do
          put $ Just elem
          return $ varC v
        _ -> return elem
    repDual c _ a1 a2 =
      ifReplaced (return $ c a1 a2) (maybeReplace (c a1 a2))
    repAbst _ v ann =
      ifReplaced (return $ abstC v ann) (maybeReplace (abstC v ann))
    alg = unionAlgebra (mkCalcAlgebra baseVar repAbst (repDual appC)) (repDual unionC) (const $ return emptyC)

mapASTAlg f = mkCalcAlgebra varF abstF appF
  where
    varF i v = f i $ varC v
    abstF i v e = f i $ abstC v e
    appF i e1 e2 = f i $ appC e1 e2

mapASTUnionAlg f = unionAlgebra (mapASTAlg f) unionF emptyF
  where
    unionF i e1 e2 = f i $ unionC e1 e2
    emptyF i = f i $ emptyC

baseProbAlg :: (Monad m, LambdaCalculus a alg) => alg m a (Ma.Map Int Int)
baseProbAlg = mkGroupCalcAlgebra varF abstF appF
  where
    varF i _ = return $ Ma.fromList [(i,1)]
    abstF i _ m = return $ Ma.insert i 1 $ Ma.map (+1) m
    appF i m1 m2 = return $ Ma.insert i 1 $ Ma.map (+1) $ Ma.union m1 m2

baseProbUnionAlg :: (Monad m, WithSets a alg, LambdaCalculus a alg) => alg m a (Ma.Map Int Int)
baseProbUnionAlg = groupUnionAlgebra baseProbAlg unionF emptyF
  where
    emptyF i = return $ Ma.fromList [(i,1)]
    unionF i m1 m2 = return $ Ma.insert i 1 $ Ma.map (+1) $ Ma.union m1 m2

redUnions :: (Ord a, WithSets a alg, LambdaCalculus a alg) => a -> a
redUnions es = runIdentity $ red es >>= go es
  where
    red = foldM baseRedUnionAlg
    go e1 e2
      | e1 == e2 = return e1
      | otherwise = red e2 >>= go e2
