{-# Language TemplateHaskell #-}
module Analysis.Algorithms.Common where
import Control.Applicative
import Control.Monad.State
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import qualified Analysis.Types.AnnType as AT
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Common as CT
import Control.Lens
import Control.Applicative()

data FreshVar = B0 | B1 | D0 deriving (Show,Eq,Ord)

-- Constraints are represented as pairs. The first
-- element is the  Annotation/Effect that must be
-- included in the annotation variable
type Constraint = (Either A.Annotation E.Effect, S.FlowVariable)

data RContext = RContext{
  _freshIx :: Int
  }

makeLenses ''RContext

data RState = RState{
  _freshFlowVars :: M.Map Int (M.Map FreshVar Int),
  _completions :: M.Map Int (AT.Type, [S.FlowVariable]),
  _gammas :: M.Map Int (M.Map Int (AT.Type, Int)),
  _fvGammas:: M.Map Int (Maybe S.Sort)
}

makeLenses ''RState

instance CT.Group RState where
  void = RState M.empty M.empty M.empty M.empty
  sa <+> sb =
    RState{
      _completions = M.union (sa ^.completions) (sb ^.completions),
      _freshFlowVars = M.union (sa ^.freshFlowVars) (sb ^. freshFlowVars),
      _gammas = M.union (sa ^. gammas) (sb ^. gammas),
      _fvGammas = M.union (sa ^. fvGammas) (sb ^. fvGammas)
      }

getFreshIx :: (Functor m, Monad m) => StateT RContext m Int
getFreshIx = do
  i <- (^.freshIx) <$> get
  modify (freshIx -~ (1))
  return i

-- fresh ix s = do
--   v <- getFreshIx
--   modify (fvGammas %~ (M.map (M.insert v s)))
--   return v
