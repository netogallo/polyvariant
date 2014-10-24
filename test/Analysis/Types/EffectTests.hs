module Analysis.Types.EffectTests where

import Test.QuickCheck
import Control.Applicative
import Analysis.Types.Effect
import qualified Analysis.Types.Annotation as A
import Analysis.Types.CommonTests
import qualified Analysis.Types.AnnotationTests as AT
import Analysis.Types.SortsTests()
import qualified Analysis.Types.Sorts as S
import Control.Monad.State
import qualified Data.Set as D

arbitraryWithSort sort' = arbitrary' [] sort'
  where
    arbitrary' gamma sort = do
      pEff <- elements [1..20]
      let varRange = [1..3]
          lbl = elements $ map show ([1..100] :: [Int])
          mkApp = do
            e1 <- arbitrary' gamma (S.Arr S.Eff sort)
            e2 <- arbitrary' gamma S.Eff
            return $ App e1 e2
          mkAppAnn = do
            e1 <- arbitrary' gamma (S.Arr S.Ann sort)
            e2 <- arbitrary
            return $ App e1 e2
      var <- case filter (\(_,sort'') -> sort == sort'') gamma of
        [] -> return Nothing
        vs -> Just . fst <$> elements vs
      eff <- case sort of
        S.Arr s1 s2 -> do
          v <- elements varRange
          eff <- arbitrary' ((v,s1) : gamma) s2
          return $ Abs (S.Var v s1) eff
        S.Eff | pEff < 5 -> Flow <$> lbl <*> arbitrary
        S.Eff | pEff < 10 -> return Empty
        S.Eff | pEff < 15 -> Union <$> arbitrary' gamma S.Eff <*> arbitrary' gamma S.Eff
        S.Eff | pEff < 18 -> mkApp
        S.Eff -> mkAppAnn
        S.Ann -> arbitrary
      alt <- elements [1..3]
      return $ case var of
        Just v | alt > 1 -> Var v
        _ -> eff

instance Arbitrary Effect where

  arbitrary = arbitraryWithSort S.Eff
  shrink x =
    case x of
      Empty -> []
      Union a1 a2 -> shrinkMerge Union a1 a2
      App a1 a2 -> shrinkMerge App a1 a2
      Abs v e -> [Empty] ++ map (Abs v) (shrink e)
      _ -> [Empty]
                                                              
    where
      shrinkMerge c a1 a2 = [Empty,a1,a2] ++ [c a1' a2' | (a1',a2') <- shrink (a1,a2)]

annReplace v eff = do
  (eff', sub) <- runStateT (foldEffectM alg eff) Nothing
  return $ case sub of
    Nothing -> Nothing
    Just sub' -> Just (eff',sub')
  where
    mRepAnn ann = do
      mRep <- lift $ AT.randomReplace v ann
      case mRep of
        Nothing -> return Nothing
        Just (ann', s) -> do
          put $ Just s
          return $ Just ann'
    repLbl _ l ann = do
      mRep <- mRepAnn ann
      case mRep of
        Nothing -> return $ Flow l ann
        Just ann' -> return $ Flow l ann'

    repAppAnn _ eff ann = do
      mRep <- mRepAnn ann
      case mRep of
        Nothing -> return $ AppAnn eff ann
        Just ann' -> return $ AppAnn eff ann'

    alg :: Algebra (StateT (Maybe A.Annotation) Gen) Effect Effect
    alg = algebra{
      fflow=repLbl,
      fappAnn=repAppAnn
      }

annBetaEq eff = do
  mRep <- annReplace var eff
  case mRep of
    Just (eff',ann) -> return $ AppAnn (Abs (S.Var var S.Ann) eff') ann
    Nothing -> return eff
  where
    var = 1 + (maximum $ 0 : (D.toList $ D.map fst $ vars eff))

randomReplace v a = do
  (ann, s) <- runStateT (foldEffectM (randomReplaceAlg v) a) Nothing
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
