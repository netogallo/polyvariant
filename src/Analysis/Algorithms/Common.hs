{-# Language TemplateHaskell #-}
module Analysis.Algorithms.Common where
import Control.Applicative
import Control.Monad.State
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import qualified Analysis.Types.AnnType as AT
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import Control.Lens

data SharedVar = B1 deriving (Show,Eq,Ord)

-- Constraints are represented as pairs. The first
-- element is the  Annotation/Effect that must be
-- included in the annotation variable
type Constraint = (Either A.Annotation E.Effect, S.FlowVariable)

data RContext = RContext{
  _freshIx :: Int,
  _annotations :: M.Map (Int,SharedVar) S.FlowVariable,
  _completions :: M.Map Int (AT.Type, [S.FlowVariable]),
  _gammas :: M.Map Int (M.Map String (AT.Type, S.FlowVariable))
  }

makeLenses ''RContext

fresh :: Monad m => StateT RContext m (S.Sort -> S.FlowVariable)
fresh = do
  v <- get
  modify (freshIx +~ (-1))
  return $ S.Var $ v^.freshIx

freshAnn :: (Monad m, Functor m) => StateT RContext m S.FlowVariable
freshAnn = (\f -> f S.Ann) <$> fresh

freshEff :: (Monad m, Functor m) => StateT RContext m S.FlowVariable
freshEff = (\f -> f S.Eff) <$> fresh
