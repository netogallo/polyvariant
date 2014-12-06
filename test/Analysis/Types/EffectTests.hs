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
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Control.Monad.Identity
import qualified Analysis.Types.Common as C

-- | Type that denotes that both of its arguments
-- should have the same normal form
data Equiv = Equiv Effect Effect deriving Show

arbitraryWithSort = arbitraryWithGammaAndSort M.empty

-- | Given an environment of variables with sorts and a sort, produce
-- a randomly generated Effect of the input sort
arbitraryWithGammaAndSort gamma' sort' = evalStateT (arbitrary' gamma' sort') 0
  where
    arbitrary' gamma sort = do
      sz <- get
      put (sz + 1)
      if sz > maxTermSize
        then return $ C.emptyG sort
        else arbitrary'' gamma sort
    arbitrary'' gamma sort = do
      pEff <- lift $ elements ([1..20] :: [Int])
      let varRange = [1..3]
          mkAnnotation = lift $ AT.arbitraryWithGammaAndSort gamma S.Ann
          lbl = lift $ elements $ map show ([1..100] :: [Int])
          mkApp = do
            e1 <- arbitrary' gamma (S.Arr S.Eff sort)
            e2 <- arbitrary' gamma S.Eff
            return $ App e1 e2
          mkAppAnn = do
            e1 <- arbitrary' gamma (S.Arr S.Ann sort)
            e2 <- mkAnnotation
            return $ AppAnn e1 e2
      var <- case filter (\(_,sort'') -> sort == sort'') $ M.toList gamma of
        [] -> return Nothing
        vs -> Just . fst <$> lift (elements vs)
      eff <- case sort of
        S.Arr s1 s2 -> do
          v <- lift $ elements varRange
          eff <- arbitrary' (M.insert v s1 gamma) s2
          return $ Abs (S.Var v s1) eff
        S.Eff | pEff < 5 -> Flow <$> lbl <*> mkAnnotation
        S.Eff | pEff < 10 -> return Empty
        S.Eff | pEff < 15 -> Union <$> arbitrary' gamma S.Eff <*> arbitrary' gamma S.Eff
        S.Eff | pEff < 18 -> mkApp
        S.Eff -> mkAppAnn
        S.Ann -> fail "Cannot make Effect of sort Ann"
      alt <- lift $ elements ([1..3] :: [Int])
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

instance Arbitrary Equiv where
  arbitrary = do
    e <- arbitrary
    Equiv e <$> randomRewrite e
  shrink a = []

annReplace v eff = do
  (eff', sub) <- runStateT (foldEffectM alg eff) Nothing
  return $ case sub of
    Nothing -> Nothing
    Just sub' -> Just (eff',sub')
  where
    mRepAnn ann = do
      curr <- get
      mRep <- lift $ AT.randomReplace v ann
      case (curr,mRep) of
        (Just _,_) -> return Nothing
        (_,Nothing) -> return Nothing
        (_,Just (ann', s)) -> do
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

annRewrite e =
  case e of
    Flow l ann -> Flow l <$> AT.randomRewrite ann
    AppAnn eff ann -> AppAnn eff <$> AT.randomRewrite ann
    _ -> return e

randomRewrite :: Effect -> Gen Effect
randomRewrite e = foldEffectM alg e
  where
    pAlg = (baseProbUnionAlg :: Algebra Identity Effect (M.Map Int Int)){
      fappAnn = \i m _ -> return $ M.insert i 1 $ M.map (+1) m,
      fflow = \i _ _ -> return $ M.fromList [(i,1)]
      }
    probs = runIdentity $ foldEffectM pAlg e
    mutate i e = do
      let p = fromJust $ M.lookup i probs
      (unionEq p e
       >>= maybeRuleProb (0,p) annRewrite
       >>= maybeRuleProb (0,p) betaEq
       >>= maybeRuleProb (0,p) annBetaEq)
      
    alg = (mapASTUnionAlg mutate){
      fappAnn = \i a1 a2 -> mutate i $ AppAnn a1 a2,
      fflow = \i l eff -> mutate i $ Flow l eff
      }

data TestMergeAbst = TMA (Effect,Effect,Effect) deriving (Show,Read)

instance Arbitrary TestMergeAbst where
  arbitrary = do
    v <- S.Var <$> elements [1..5] <*> arbitrary
    let gamma = M.fromList [(S.name v,S.sort v)]
        mkEff = Abs v <$> arbitraryWithGammaAndSort gamma S.Eff
    e1 <- mkEff
    e2 <- mkEff
    e3 <- arbitrary
    return $ TMA (e1,e2,e3)

redUnionEq (TMA (Abs v e1,Abs _ e2,e3)) =
  let comp = C.unions $ redUnions $ Abs v (Union e1 e2)
  in case C.unions $ redUnions $ Set $ D.fromList [Abs v e1,e3,Abs v e2] of
        Set res -> D.member comp res
        res -> res == comp

normalizeEquivalent (Equiv a b) = normalize a == normalize b
