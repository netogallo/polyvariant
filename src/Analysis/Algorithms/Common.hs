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

freshIx :: Lens' RContext Int
freshIx _f_aKJ7 (RContext __freshIx'_aKJ8 __fvGammas_aKJa)
      = ((\ __freshIx_aKJ9 -> RContext __freshIx_aKJ9 __fvGammas_aKJa)
         <$> (_f_aKJ7 __freshIx'_aKJ8))
{-# INLINE freshIx #-}
fvGammas :: Lens' RContext (M.Map Int SortConstraint)
fvGammas _f_aKJb (RContext __freshIx_aKJc __fvGammas'_aKJd)
      = ((\ __fvGammas_aKJe -> RContext __freshIx_aKJc __fvGammas_aKJe)
         <$> (_f_aKJb __fvGammas'_aKJd))
{-# INLINE fvGammas #-}

completions :: Lens' RState (M.Map Int (AT.Type, [S.FlowVariable]))
completions
      _f_aKLO
      (RState __freshFlowVars_aKLP __completions'_aKLQ __gammas_aKLS)
      = ((\ __completions_aKLR
            -> RState __freshFlowVars_aKLP __completions_aKLR __gammas_aKLS)
         <$> (_f_aKLO __completions'_aKLQ))
{-# INLINE completions #-}
freshFlowVars :: Lens' RState (M.Map Int (M.Map FreshVar Int))
freshFlowVars
      _f_aKLT
      (RState __freshFlowVars'_aKLU __completions_aKLW __gammas_aKLX)
      = ((\ __freshFlowVars_aKLV
            -> RState __freshFlowVars_aKLV __completions_aKLW __gammas_aKLX)
         <$> (_f_aKLT __freshFlowVars'_aKLU))
{-# INLINE freshFlowVars #-}
gammas :: Lens' RState (M.Map Int (M.Map Int (AT.Type, Int)))
gammas
      _f_aKLY
      (RState __freshFlowVars_aKLZ __completions_aKM0 __gammas'_aKM1)
      = ((\ __gammas_aKM2
            -> RState __freshFlowVars_aKLZ __completions_aKM0 __gammas_aKM2)
         <$> (_f_aKLY __gammas'_aKM1))
{-# INLINE gammas #-}


rcontext = RContext (-1) M.empty

-- makeLenses ''RContext

data RState = RState{
  _freshFlowVars :: M.Map Int (M.Map FreshVar Int),
  _completions :: M.Map Int (AT.Type, [S.FlowVariable]),
  _gammas :: M.Map Int (M.Map Int (AT.Type, Int))
}

instance Show RState where
  show s = show $ _freshFlowVars s

-- makeLenses ''RState

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
