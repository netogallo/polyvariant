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

data Type =
  TBool
  | Arr Type E.Effect Type
  | Ann Type A.Annotation
  | Forall S.FlowVariable Type
  deriving (Show,Read,Eq,Ord)

instance C.LambdaCalculus Type Algebra where
  lambdaDepths = depths
  foldM = foldTypeM
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

data Algebra m a =
  Algebra{
    farr :: Int -> a -> E.Effect -> a -> m a,
    fann :: Int -> a -> A.Annotation -> m a,
    fforall :: Int -> S.FlowVariable -> a -> m a,
    ftbool :: Int -> m a
    }

algebra :: Monad m => Algebra m Type
algebra = Algebra{
  farr = \_ a1 eff a2 -> return $ Arr a1 eff a2,
  fann = \_ a1 ann -> return $ Ann a1 ann,
  fforall = \_ v a1 -> return $ Forall v a1,
  ftbool = \_ -> return TBool
  }

foldTypeM :: Monad m => Algebra m a -> Type -> m a
foldTypeM f@Algebra{..} a0 = evalStateT (foldTypeM' undefined a0) 0
  where
    foldTypeM' s a = do
      i <- get
      put (i+1)
      case a of
        TBool -> lift $ ftbool i
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
      ftbool = \_ -> return M.empty
      }

renameByLambdasOffset base offset obj = lift calcReplacements >>= mkReplacements
  where
    repAlg = Algebra{
      farr = \i a1 _ a2 -> C.rename2 base i a1 a2,
      fann = \i a1 _ -> C.rename1 base i a1,
      fforall = C.renameAbs base offset obj,
      ftbool = const (return M.empty)
      }
    calcReplacements = C.foldM repAlg obj
    arr rep i t1 eff t2 = do
      let offset' = fromJust $ M.lookup i $ C.lambdaDepths (obj :: Type)
          base' = fromJust $ M.lookup i rep
      eff' <- E.renameByLambdasOffset base' offset' eff
      return $ Arr t1 eff' t2
    subAlg rep = algebra{
      farr = arr rep,
      fann = A.subAppAnn Ann obj rep
      }
    mkReplacements rep = C.foldM (subAlg rep) obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int,M.empty)
