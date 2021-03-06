{-# Language RecordWildCards, MultiParamTypeClasses #-}
module Analysis.Types.AnnType where
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as M
import qualified Analysis.Types.Common as C
import Data.Maybe
import Control.Applicative
import qualified Data.Set as D

data Type =
  -- | Type constructor for boolean
  TBool
  -- | Type constructor for arrow types
  | Arr Type E.Effect Type
  -- | Type Constructor to add an annotation to a type
  | Ann Type A.Annotation
  -- | Constructor for quantification over annotation or effect variables
  | Forall S.FlowVariable Type
  -- | Not supported. Only used for nicer error messages
  | Var Int
  deriving (Show,Read,Eq,Ord)

instance C.Fold Type Algebra where    
  foldM = foldTypeM
  baseAlgebra = algebra
  groupAlgebra =
    Algebra{
      ftbool = \_ -> return C.void,
      fforall = \_ _ s -> return s,
      fann = \_ s _ -> return s,
      farr = \_ s1 _ s2 -> return $ s1 C.<+> s2,
      fvar = \_ i -> return C.void
      }
  byId i e = runIdentity $ execStateT (C.foldM alg e) Nothing
    where
      putElem i' e' = do
        unless (i /= i') $ put (Just e')
        return e'
          
      alg = Algebra{
        farr = \i' t1 eff t2 -> putElem i' $ Arr t1 eff t2,
        fann = \i' t1 ann -> putElem i' $ Ann t1 ann,
        fforall = \i' v t -> putElem i' $ Forall v t,
        ftbool = \i' -> putElem i' TBool
        }

instance C.WithAbstraction Type Algebra where
    lambdaDepths = depths
    abst (Forall v t) = Just (v,t)
    abst _ = Nothing
    abstC = Forall
    baseAbstAlgebra alg abst = alg{fforall=abst}
    groupAbstAlgebra alg abst = alg{fforall=abst}

data Algebra m t a =
  Algebra{
    farr :: Int -> a -> E.Effect -> a -> m a,
    fann :: Int -> a -> A.Annotation -> m a,
    fforall :: Int -> S.FlowVariable -> a -> m a,
    ftbool :: Int -> m a,
    fvar :: Int -> Int -> m a
    }

algebra :: Monad m => Algebra m t Type
algebra = Algebra{
  farr = \_ a1 eff a2 -> return $ Arr a1 eff a2,
  fann = \_ a1 ann -> return $ Ann a1 ann,
  fforall = \_ v a1 -> return $ Forall v a1,
  ftbool = \_ -> return TBool,
  fvar = \_ i -> return $ Var i
  }

foldTypeM :: Monad m => Algebra m Type a -> Type -> m a
foldTypeM f@Algebra{..} a0 = evalStateT (foldTypeM' undefined a0) 0
  where
    foldTypeM' s a = do
      i <- get
      put (i+1)
      case a of
        TBool -> lift $ ftbool i
        Var v -> lift $ fvar i v
        Ann t1 ann -> do
          t1' <- foldTypeM' s t1
          lift $ fann i t1' ann
        Arr t1 eff t2 -> do
          t1' <- foldTypeM' s t1
          t2' <- foldTypeM' s t2
          lift $ farr i t1' eff t2'
        Forall v t1 ->
          foldTypeM' s t1 >>= lift . (fforall i v)

depths = runIdentity . (C.foldM alg)
  where
    alg = Algebra{
      farr = \i d1 _ d2 -> return $ M.insert i 0 $ M.union d1 d2,
      fann = \i d _ -> return $ M.insert i 0 d,
      fforall = \i _ d1 -> return $ M.insert i 0 $ M.map (+(1 :: Int)) d1,
      ftbool = \_ -> return M.empty,
      fvar = \_ _ -> return M.empty
      }

renameByLambdasOffset base'' offset obj = calcReplacements >>= mkReplacements
  where
    base = C.mkRepBase base''
    repAlg = (C.baseRepAbstAlg base'' offset obj :: Monad m => Algebra m Type (M.Map Int (M.Map Int (Int,Bool)))){
      farr = \i a1 _ a2 -> return $ M.insert i base $ M.union a1 a2,
      fann = \i a1 _ -> return $ M.insert i base a1,
      ftbool = \i -> return $ M.fromList [(i,base)]
      }
    calcReplacements = M.map (M.map fst) <$> C.foldM repAlg obj
    arr rep i t1 eff t2 = do
      let offset' = fromJust $ M.lookup i $ C.lambdaDepths (obj :: Type)
          base' = fromJust $ M.lookup i rep
      eff' <- E.renameByLambdasOffset base' offset' eff
      return $ Arr t1 eff' t2
    ann rep i t ann =
      let offset' = fromJust $ M.lookup i $ C.lambdaDepths (obj :: Type)
          base' = fromJust $ M.lookup i rep
      in Ann t <$> A.renameByLambdasOffset base' offset' ann
    subAlg rep = (C.baseSubAbstAlg rep){
      farr = arr rep,
      fann = ann rep
      }
    mkReplacements rep = C.foldM (subAlg rep) obj

renameByLambdas obj = runIdentity $ renameByLambdasOffset M.empty 0 obj

reduce' = runIdentity . foldTypeM alg
  where
    arrF _ t1 e t2 = return $ Arr t1 (C.unions $ E.reduce e) t2
    annF _ t1 ann = return $ Ann t1 $ C.unions $ A.reduce ann
    alg = algebra{
      fann = annF,
      farr = arrF
      }

getBoundVars :: Type -> M.Map Int (D.Set Int)
getBoundVars = runIdentity . foldTypeM alg
  where
    alg = (C.boundedVarsAlg :: Algebra Identity Type (M.Map Int (D.Set Int))) {
      fann=annF,
      farr=arrF}
    annF i s _ = return $ M.insert i D.empty s
    arrF i s1 _ s2 = return $ M.insert i D.empty $ M.union s1 s2

replaceFree :: M.Map Int (Either A.Annotation E.Effect) -> Type -> Type
replaceFree rep type' = runIdentity $ foldTypeM alg type'
  where
    (annReps,_) = M.mapEither id rep
    boundVars i = (\(Just w_1919) -> w_1919) $ M.lookup i $ getBoundVars type'
    isBound i v = D.member v $ boundVars i
    annReplacements i = M.filterWithKey (\k _ -> not (isBound i k)) annReps
    effReplacements i = M.filterWithKey (\k _ -> not (isBound i k)) rep
    annF i s ann = return $ Ann s $ A.replaceFree (annReplacements i) ann
    arrF i s1 eff s2 = return $ Arr s1 (E.replaceFree (effReplacements i) eff) s2
    alg = algebra{
      fann=annF,farr=arrF}

vars :: Type -> D.Set (Int,C.Boundness)
vars = runIdentity . C.foldM alg
  where
    arrF _ s1 eff s2 = return $ D.unions [s1,s2,E.vars eff]
    annF _ s a = return $ D.unions [s,A.vars a]
    alg = (C.baseAbstVarsAlg :: Algebra Identity Type (D.Set (Int,C.Boundness))){
      farr = arrF,
      fann = annF
      }

reduce e = if reduce' e == e then e else reduce $ reduce' e

normalize = reduce . renameByLambdas
