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
import Data.Maybe (isJust,fromJust)

data Equiv = Equiv Annotation Annotation deriving Show

arbitraryWithGammaAndSort :: M.Map Int S.Sort -> S.Sort -> Gen Annotation
arbitraryWithGammaAndSort gamma' sort' = arbitrary' (0 :: Int) gamma' sort'
   where
      arbitrary' pUn gamma sort = do
        p <- choose (0,99) :: Gen Int
        let varRange = elements $ [1..3]
            lbl = elements $ map show [1..100]
        var <- case filter ((== sort) . snd) $ M.toList gamma of
          [] -> return Nothing
          vs -> Just . fst <$> elements vs
          
        ann' <- case sort of
          S.Eff -> error "Annotations cannot have effect in the Sort"
          S.Ann | p `mod` 2 < 1 -> return Empty
          S.Ann -> Label <$> lbl
          S.Arr a1 a2 -> do
            v <- varRange
            ann <- arbitrary' pUn (M.insert v a1 gamma) a2
            return $ Abs (S.Var v a1) ann
            
        pOver <- choose (0,99) :: Gen Int
        ann' <- case var of
          _ | pOver `mod` 10  < 1 -> do
            ann1 <- arbitrary' pUn gamma (S.Arr S.Ann sort)
            ann2 <- arbitrary' pUn gamma sort
            return $ App ann1 ann2
          Just v | pOver `mod` 3 > 0 -> return $ Var v
          _ -> return ann'
          
        pUn' <- choose (1,pUn + 7)
        case sort of
          S.Ann | pUn' < 5 -> do
            u1 <- arbitrary' (pUn + 1) gamma' sort'
            u2 <- arbitrary' (pUn + 1) gamma' sort'
            return $ Union (Union u1 u2) ann'
          _ -> return ann'

instance Arbitrary Annotation where
  arbitrary = arbitraryWithGammaAndSort M.empty S.Ann
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

randomRewrite ann = evalStateT (randomRewrite' ann) 1
  where
    randomRewrite' e'' = do
      p <- get
      put (p + 1)
      e <- lift $ CT.maybeRuleProb (0,p) betaEq e''
      case e of
        e'@(Union _ _) -> do
          e'' <- lift $ CT.unionEq p e'
          case e'' of
            Union a b -> Union <$> randomRewrite' a <*> randomRewrite' b
            -- The rewrite resulted in an empty set (is possible)
            _ -> return e''
        (App (Abs v e1) e2) -> do
          (\x -> App (Abs v x)) <$> randomRewrite' e1 <*> randomRewrite' e2
        Abs v e1 -> Abs v <$> randomRewrite' e1
        App a b -> App <$> randomRewrite' a <*> randomRewrite' b
        Empty -> lift $ CT.maybeRuleProb (0,p) CT.identEq Empty
        a -> return a
    
normalizeEquivalent (Equiv a b) = normalize a == normalize b
