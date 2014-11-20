{-# Language TemplateHaskell #-}
module Analysis.Algorithms.Common where
import Analysis.Common
import Control.Applicative
import Control.Monad.State
import Analysis.Types.Render ()
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import qualified Analysis.Types.AnnType as AT
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Common as CT
import Control.Lens
import Control.Applicative()
import Text.LaTeX.Packages.AMSMath
import Text.LaTeX.Base.Texy
import Text.LaTeX.Base
import Text.LaTeX.Base.Class

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

-- (Result type, constraints, Label, beta, delta)
type LogResult = (AT.Type, [(Either A.Annotation E.Effect,Int)], Int, Int, Int)

data LogEntry =
  BasicLog LogResult
  -- | Base results, tau1, [Chi_i::s_i], X, Psi2, Phi0
  | AbstLog LogResult AT.Type [(Int,S.Sort)] [(Int,S.Sort)] A.Annotation E.Effect
  -- | Base results, I(tau1), Omega
  | AppLog LogResult AT.Type (M.Map Int (Either A.Annotation E.Effect))
  -- | Base results, I(tau1), Omega1, Omega2
  | FixLog LogResult AT.Type (M.Map Int (Either A.Annotation E.Effect)) (M.Map Int (Either A.Annotation E.Effect))
  deriving Show

renderBase (t,cs,l,b,d) =
  let
    eRender (e,v) =
      case e of
        Left a -> subset (texy a) (texy (A.Var v)) :: LaTeX
        Right e -> subset (texy e) (texy (E.Var v)) :: LaTeX
    cs' = map eRender cs
    l' = (renderLbl (show l) :: LaTeX)
  in (texy t, texy cs', l', texy $ A.Var b, texy $ E.Var d)

renderVar (v,s)
  | S.annSort s = texy (A.Var v) <> stexy "::" <> texy s
  | otherwise = texy (E.Var v) <> stexy "::" <> texy s

renderLog l =
  let
    asRows :: LogResult -> [(LaTeX,LaTeX)]
    asRows b' =
      let (b1,b2,b3,b4,b5) = renderBase b'
      in [(tau,b1),(mathit (stexy "C"),b2),(mathit (stexy "l"),b3),(beta,b4),(delta,b5)]
    iRender t = (mathbf (stexy "I") <> autoParens (tau !: stexy "1"), texy t)
    rows = case l of
        BasicLog r -> asRows r
        AbstLog r t1 chis x psi2 phi0 ->
          asRows r ++
          [
            (tau !: stexy "1", texy t1),
            (bar $ texy (chi !: stexy "i" <> stexy "::" <> stexy "s" !: stexy "i" :: LaTeX), texy $ (map renderVar chis :: [LaTeX])),
            (texy "X", texy $ (map renderVar x :: [LaTeX])),
            (psi !: stexy "2", texy psi2),
            (phi !: stexy "0", texy phi0)
          ]
        AppLog r i rep1 ->
          asRows r ++
          [
            iRender i,
            (theta, texy rep1)
          ]
        FixLog r i rep1 rep2 ->
          asRows r ++
          [
            iRender i,
            (theta !: stexy "1",texy rep1),
            (theta !: stexy "2",texy rep2)
          ]
    mkTableRow s (e,v) = e Text.LaTeX.Base.& v <> lnbk <> s
  in tabular Nothing [CenterColumn,CenterColumn] (foldl mkTableRow mempty rows)
          

instance Texy LogEntry where
  texy = texy . renderLog

data RContext = RContext{
  _freshIx :: Int,
  _fvGammas:: M.Map Int SortConstraint,
  _history :: [LogEntry]
 }

rcontext = RContext (-1) M.empty []

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
