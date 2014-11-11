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

data SortConstraint =
  AnyEffect
  | AnyAnnotation
  | ASort S.Sort
  deriving (Show,Eq)
                                                  

isAnnConstraint c =
  case c of
    AnyAnnotation -> True
    ASort s -> S.annSort s

-- Constraints are represented as pairs. The first
-- element is the  Annotation/Effect that must be
-- included in the annotation variable
type Constraint = (Either A.Annotation E.Effect, Int)

data RContext = RContext{
  _freshIx :: Int,
  _fvGammas:: M.Map Int SortConstraint
 }

rcontext = RContext (-1) M.empty

makeLenses ''RContext

data RState = RState{
  _freshFlowVars :: M.Map Int (M.Map FreshVar Int),
  _completions :: M.Map Int (AT.Type, [S.FlowVariable]),
  _gammas :: M.Map Int (M.Map Int (AT.Type, Int))
}

instance Show RState where
  show s = show $ _freshFlowVars s

makeLenses ''RState

instance CT.Group RState where
  void = RState M.empty M.empty M.empty
  sa <+> sb =
    RState{
      _completions = M.union (_completions sa) (_completions sb),
      _freshFlowVars = M.unionWith M.union (_freshFlowVars sa) (_freshFlowVars sb),
      _gammas = M.unionWith M.union (_gammas sa) (_gammas sb)
      }

getFreshIx :: (Functor m, Monad m) => SortConstraint -> StateT RContext m Int
getFreshIx sort = do
  i <- (^.freshIx) <$> get
  modify (freshIx -~ (1))
  modify (fvGammas %~ M.insert i sort)
  return i

updateSort var sort = modify (fvGammas %~ M.insert var sort)

-- fresh ix s = do
--   v <- getFreshIx
--   modify (fvGammas %~ (M.map (M.insert v s)))
--   return v
