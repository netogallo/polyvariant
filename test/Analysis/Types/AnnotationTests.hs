module Analysis.Types.AnnotationTests where

import Analysis.Types.Annotation
import qualified Analysis.Types.Sorts as S
import qualified Analysis.Types.Common as C
import qualified Analysis.Types.CommonTests as CT
import Test.QuickCheck.Gen
import Test.QuickCheck
import Control.Applicative
import Control.Monad (foldM, (>=>))
import qualified Data.Map as M
import Control.Monad.State
import qualified Data.Set as D

data Equiv = Equiv Annotation Annotation deriving Show

instance Arbitrary Annotation where
  arbitrary = mkBound <$> arbitrary'
    where
      arbitrary' = do
        s <- elements [1..7]
        let var = elements $ [1..3]
            lbl = elements $ map show [1..100]
        case s of
          1 -> Var <$> var
          2 -> Union <$> arbitrary' <*> arbitrary'
          3 -> (\v t -> App (Abs (S.Var v S.Ann) t)) <$> var <*> arbitrary' <*> arbitrary'
          4 -> (\v -> Abs (S.Var v S.Ann)) <$> var <*> arbitrary'
          5 -> Label <$> lbl
          6 -> (\v -> App (Var v)) <$> var <*> arbitrary'
          _ -> return Empty
      mkBound expr =
        let
          free = D.filter (not . C.bound) $ vars expr
        in D.fold (\(v,_) s -> Abs (S.Var v S.Ann) s) expr free
          
  shrink x =
    case x of
      Empty -> []
      Union a1 a2 -> shrinkMerge Union a1 a2
      App a1 a2 -> shrinkMerge App a1 a2
      Abs v e -> [Empty] ++ map (Abs v) (shrink e)
      _ -> [Empty]
                                                              
    where
      shrinkMerge c a1 a2 = [Empty,a1,a2] ++ [c a1' a2' | (a1',a2') <- shrink (a1,a2)]

instance Arbitrary Equiv where
  arbitrary = do
    e <- arbitrary
    Equiv e <$> randomRewrite e
  shrink x = []

(\\) (_:xs) 0 = xs
(\\) (x:xs) i = x : xs \\ (i-1)

shuffle s' = snd <$> (foldM cata (s',[]) $ replicate (length s') ())
  where
    cata (s,e) _ = do
      i <- choose (0,length s - 1)
      return (s \\ i,s !! i : e)

asocEq x@(Union _ _) = do
  e:es <- shuffle $ unionGen [Empty] (:[]) concat x
  return $ foldl Union e es
asocEq a = return a

emptyEq (Union a b) = do
  which <- arbitrary
  if which
    then return $ Union a $ Union b Empty
    else return $ Union (Union a Empty) b
emptyEq a = return a

identEq Empty = do
  which <- arbitrary
  if which
    then return $ Union Empty Empty
    else return Empty
identEq (Union a b) = do
  which <- arbitrary
  if which
    then return $ Union a $ Union b b
    else return $ Union (Union a a) b
identEq a = return a

maybeRuleProb p r s = do
  apply <- choose p
  if apply <= (1 :: Int)
    then r s
    else return s

maybeRule = maybeRuleProb (0,1)

randomReplace v a = do
  (ann, s) <- runStateT (foldAnnM (CT.randomReplaceAlg v) a) Nothing
  case s of
    Nothing -> return Nothing
    Just s' -> return $ Just (ann, s')      

betaEq a = do
  mRep <- randomReplace var a
  case mRep of
    Just (a', exp) -> return $ App (Abs (S.Var var S.Ann) a') exp
    Nothing -> return a
  where
    var = 1 + (maximum $ 0 : (D.toList $ D.map fst $ vars a))
    

unionEq p = maybeRuleProb (1,p) asocEq >=> maybeRuleProb (1,p) identEq >=> maybeRuleProb (1,p) emptyEq

randomRewrite ann = evalStateT (randomRewrite' ann) 1
  where
    randomRewrite' e'' = do
      p <- get
      put (p + 1)
      e <- lift $ maybeRuleProb (1,p) betaEq e''
      case e of
        e'@(Union _ _) -> do
          Union a b <- lift $ unionEq p e'
          Union <$> randomRewrite' a <*> randomRewrite' b
        (App (Abs v e1) e2) -> do
          (\x -> App (Abs v x)) <$> randomRewrite' e1 <*> randomRewrite' e2
        Abs v e1 -> Abs v <$> randomRewrite' e1
        App a b -> App <$> randomRewrite' a <*> randomRewrite' b
        Empty -> lift $ maybeRuleProb (1,p) identEq Empty
        a -> return a
    
normalizeEquivalent (Equiv a b) = normalize a == normalize b
