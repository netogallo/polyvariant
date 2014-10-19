{-# Language RecordWildCards, MultiParamTypeClasses #-}
module Analysis.Types.Effect where
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S
import qualified Data.Set as D
import Control.Monad.State
import qualified Data.Map as M
import Data.Maybe
import Control.Monad.Identity
import qualified Analysis.Types.Common as C

data Effect =
  Var Int
  | App Effect Effect
  | AppAnn Effect A.Annotation
  | Abs S.FlowVariable Effect
  | Union Effect Effect
  | Flow String A.Annotation
  | Empty
  | Set (D.Set Effect)
  deriving (Show,Read,Ord,Eq)

instance C.LambdaCalculus Effect Algebra where
  lambdaDepths = depths
  foldM = foldEffectM
  byId = undefined


data Algebra m a =
  Algebra {
    fvar :: Int -> Int -> m a,
    fapp :: Int -> a -> a -> m a,
    fappAnn :: Int -> a -> A.Annotation -> m a,
    fabs :: Int -> S.FlowVariable -> a -> m a,
    funion :: Int -> a -> a -> m a,
    fflow :: Int -> String -> A.Annotation -> m a,
    fempty :: Int -> m a
    }

algebra :: Monad m => Algebra m Effect
algebra = Algebra{
  fvar = \_ v -> return $ Var v,
  fapp = un App,
  funion = un Union,
  fabs = \_ v s -> return $ Abs v s,
  fflow = \_ lbl ann -> return $ Flow lbl ann,
  fappAnn = \_ s ann -> return $ AppAnn s ann,
  fempty = \_ -> return Empty
  }
  where
    un c _ a1 a2 = return $ c a1 a2

foldEffectM f@Algebra{..} a0 = evalStateT (foldEffectM' undefined a0) 0
  where
    foldEffectM' s a = do
      i <- get
      put (i+1)
      let
        go fn a1 a2 = do
          a1' <- foldEffectM' s a1
          a2' <- foldEffectM' s a2
          lift $ fn i a1' a2'
      case a of
        App a1 a2 -> go fapp a1 a2
        Union a1 a2 -> go funion a1 a2
        Set as -> foldEffectM' s $ foldl Union Empty $ D.toAscList as
        Var v -> lift $ fvar i v
        Abs v a1 -> (foldEffectM' s a1) >>= (lift . (fabs i v))
        AppAnn a1 a2 -> (foldEffectM' s a1) >>= \s' -> lift $ fappAnn i s' a2
        Flow l a1 -> lift $ fflow i l a1
        Empty -> lift $ fempty i

depths = runIdentity . (foldEffectM alg) 
  where
    alg = Algebra {
      fapp = un,
      funion = un,
      fabs = \i _ s -> return $ M.insert i 0 $ M.map (+1) s,
      fvar = sing,
      fappAnn = \i s _ -> return $ M.insert i 0 $ M.map (+1) s,
      fflow = \i _ _ -> return $ M.insert i 0 M.empty,
      fempty = const (return M.empty)
      }
    sing i _ = return $ M.insert i 0 M.empty
    un i ma mb = return $ M.insert i 0 $ M.union ma mb
    
renameByLambdasOffset base offset obj = lift calcReplacements >>= mkReplacements
  where
    calcReplacements = foldEffectM repAlg obj
    repAlg = Algebra{
      fvar = C.discard $ C.rename base,
      fapp = C.rename2 base,
      fappAnn = \i s _ -> C.rename1 base i s,
      fabs = C.renameAbs base offset obj,
      funion = C.rename2 base,
      fflow = C.discard $ C.discard $ C.rename base,
      fempty = const (return M.empty)
      }
    subAlg rep =  algebra{
      fvar = C.subVar Var rep,
      fabs = C.subAbs Abs rep,
      fappAnn = A.subAppAnn AppAnn obj rep
      }
    mkReplacements rep = foldEffectM (subAlg rep) obj

renameByLambdas obj = runIdentity $ evalStateT (renameByLambdasOffset M.empty 0 obj) (-1 :: Int, M.empty)
