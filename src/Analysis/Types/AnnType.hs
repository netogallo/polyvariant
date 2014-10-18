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
  deriving (Show,Read)

instance C.LambdaCalculus Type Algebra where
  lambdaDepths = depths
  foldM = foldTypeM
  byId = undefined

data Algebra m a =
  Algebra{
    farr :: Int -> a -> E.Effect -> a -> m a,
    fann :: Int -> a -> A.Annotation -> m a,
    fforall :: Int -> S.FlowVariable -> a -> m a
    }

algebra :: Monad m => Algebra m Type
algebra = Algebra{
  farr = \_ a1 eff a2 -> return $ Arr a1 eff a2,
  fann = \_ a1 ann -> return $ Ann a1 ann,
  fforall = \_ v a1 -> return $ Forall v a1
  }

foldTypeM :: Monad m => Algebra m a -> a -> Type -> m a
foldTypeM f@Algebra{..} s0 a0 = evalStateT (foldTypeM' s0 a0) 0
  where
    foldTypeM' s a = do
      i <- get
      put (i+1)
      case a of
        TBool -> return s
        Ann t1 ann -> do
          t1' <- foldTypeM' s t1
          lift $ fann i t1' ann
        Arr t1 eff t2 -> do
          t1' <- foldTypeM' s t1
          t2' <- foldTypeM' s t2
          lift $ farr i t1' eff t2'
        Forall v t1 ->
          foldTypeM' s t1 >>= lift . (fforall i v)

depths = runIdentity . (C.foldM alg M.empty)
  where
    alg = Algebra{
      farr = \i d1 _ d2 -> return $ M.insert i 0 $ M.union d1 d2,
      fann = \i d _ -> return $ M.insert i 0 d,
      fforall = \i _ d1 -> return $ M.insert i 0 $ M.map (+(1 :: Int)) d1
      }

renameByLambdasOffset base offset obj = lift calcReplacements >>= mkReplacements
  where
    repAlg = Algebra{
      farr = \i a1 _ a2 -> C.rename2 base i a1 a2,
      fann = \i a1 _ -> C.rename1 base i a1,
      fforall = C.renameAbs base offset obj
      }
    calcReplacements = C.foldM repAlg M.empty obj
    arr rep i t1 eff t2 = do
      let offset' = fromJust $ M.lookup i $ C.lambdaDepths (obj :: Type)
          base' = fromJust $ M.lookup i rep
      eff' <- E.renameByLambdasOffset base' offset' eff
      return $ Arr t1 eff' t2
    subAlg rep = algebra{
      farr = arr rep,
      fann = A.subAppAnn Ann obj rep
      }
    mkReplacements rep = C.foldM (subAlg rep) TBool obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int,M.empty)
