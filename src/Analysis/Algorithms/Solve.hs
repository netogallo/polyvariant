{-# Language FlexibleContexts #-}
module Analysis.Algorithms.Solve where

import Control.Lens
import Control.Applicative
import Analysis.Algorithms.Common
import qualified Analysis.Types.Common as C
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Sorts as S
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as D
import Control.Monad
import Control.Monad.State
import Control.Monad.Except


-- | Helper function that iterates over elements of the constraint queue
-- until all constraints are resolved. The algorithm checks wether an
-- expression A is a subset of another expression B by normalizing
-- B and B `union` A and checking wether they are equal. The algorithm
-- Also takes a list of dependencies such that when a new value is calculated
-- for a variable under analysis, all expressions containing that variable
-- are analyzed again
solveIt :: (MonadError RFailure m, MonadState RContext m) =>
           Int ->
           M.Map Int (D.Set (Either A.Annotation E.Effect, Int)) ->
           StateT (D.Set (Either A.Annotation E.Effect, Int), M.Map Int (Either A.Annotation E.Effect)) m ()
solveIt l deps = do
  (worklist,analysis) <- get
  unless (D.size worklist == 0) $ do
    let (e',x) = D.elemAt 0 worklist
    e <- lookupExpr e'
    let (e1,e2) = (e,(\(Just w_1919) -> w_1919) $ M.lookup x analysis)
    (analysis', isSubset) <- case (e1,e2) of
          (Left a1, Left a2) | A.normalize (A.Union a1 a2) /= A.normalize a2 ->
            return (M.insert x (Left $ A.Union a1 a2) analysis, False)
          (Left _, Left _) -> return (analysis, True)
          (Right e1, Right e2) | E.normalize (E.Union e1 e2) /= E.normalize e2 ->
            return (M.insert x (Right $ E.Union e1 e2) analysis, False)
          (Right _, Right _) -> return (analysis, True)
          (a,b) -> lift $ throwError $ Failure l [
            toMsg "Inconsistent annotations and effect mix: ",
            toMsg a, toMsg " and ", toMsg b]
    let worklist' = if isSubset
                    then D.deleteAt 0 worklist
                    else D.unions [D.deleteAt 0 worklist,fromMaybe D.empty $ M.lookup x deps]
    put (worklist',analysis')
    solveIt l deps
  where
    -- Function that when provided with an expression and the analysis so far,
    -- replaces all the free variables of the expression with the value determined
    -- so far by the analysis
    lookupExpr e = do
      analysis <- use _2
      let (annAnalysis,_) = M.mapEither id analysis
      return $ case e of
        Left ann -> Left $ A.replaceFree annAnalysis ann
        Right eff -> Right $ E.replaceFree analysis eff

-- | The constraint solver. Given a list of subset relations, this
-- algorithm determines which is the minimal set suitable for the variables
-- being ananalized. It takes as input the a list of constraints (c)
-- list of constants (x), b and d which are the Annotation and Effect
-- variables being analyzed
solve l c x b d = do
  -- Initialize the analysis map assigning to all
  -- variables appearing in the constraints the empty element
  -- as result, beta and delta also start with the empty element
  -- and the list of constants are constrained to be a subset
  -- of themselves
  analysis <- (\x y z -> M.fromList $ x ++ y ++ z)
              <$> mapM (analysisM . snd) c
              <*> (mapM analysisM $ [b,d])
              <*> mapM analysisC x
  -- Initialize the list of dependencies by looking at all the
  -- free variables of an expression and making that expression
  -- dependent on the dependencies of the free variables that
  -- appear in it.
  deps <- return (foldl depsInit M.empty (map fst c))
              >>= return . (\s0 -> foldl depsExtend s0 c)

  -- Initalize the worklist by simply listing all the constraints
  -- that need to be solved
  let worklist = D.fromList c
  (_,res) <- execStateT (solveIt l deps) (worklist,analysis)
  case ((\(Just x) -> x) $ M.lookup b res, (\(Just x) -> x) $ M.lookup d res) of
    (Left ann, Right eff) -> return (ann,eff)
    (a,b) -> throwError $ Failure l [
        toMsg "Invalid result for solve: ",
        toMsg " the value ", toMsg a,
        toMsg " was expected to be an annotation ",
        toMsg " and the value ", toMsg b,
        toMsg " was expected to be an effect"]  

  where
    -- Function that constraints constants. It looksup the
    -- sort of the free variables in the sort environment
    -- and creates the appropiate constraint
    analysisC v = do
      s' <- ((\(Just x) -> x) . M.lookup v) <$> use fvGammas
      return $ if isAnnConstraint s'
        then (v,Left $ A.Var v)
        else (v,Right $ E.Var v)
    -- Function that constrains a variable to the empty element
    -- the empty element is calculated depending on the sort
    -- of the variable by looking it up in the free variable
    -- environment
    analysisM v = do
      s' <- ((\(Just x) -> x) . M.lookup v) <$> use fvGammas
      return $ (v,emptyTerm s')

    freeVars expr' =
      let vars expr = map fst $ filter (not . C.bound) $ D.toList $ C.vars expr
      in case expr' of
        Right e -> vars e
        Left e -> vars e
    depsInit :: M.Map Int (D.Set (Either A.Annotation E.Effect,Int)) -> Either A.Annotation E.Effect -> M.Map Int (D.Set (Either A.Annotation E.Effect,Int))
    depsInit deps expr = foldl (\s v -> M.insert v D.empty s) deps $ freeVars expr
    depsExtend :: M.Map Int (D.Set (Either A.Annotation E.Effect,Int)) -> (Either A.Annotation E.Effect,Int) -> M.Map Int (D.Set (Either A.Annotation E.Effect,Int))
    depsExtend deps c'@(expr,_) = foldl (\s v -> M.insertWith D.union v (D.singleton c') s) deps $ freeVars expr
          
