{-# Language RecordWildCards, MultiParamTypeClasses #-}
module Analysis.Types.AnnType where
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map as M
import qualified Analysis.Types.Common as C

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

-- renameByLambdasOffset base offset obj = lift calcReplacements >>= mkReplacements
--  where
--    forall i v s = undefined
