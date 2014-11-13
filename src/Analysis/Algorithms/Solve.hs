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

import Debug.Trace

emptyG s' = evalState (go s') 1
  where
    go s =
      case s of
        S.Eff -> return C.emptyC
        S.Ann -> return C.emptyC
        S.Arr s1 s2 -> do
          i <- get
          modify (+1)
          C.abstC (S.Var i s1) <$> go s2

emptyTerm :: SortConstraint -> Either A.Annotation E.Effect
emptyTerm s' =
  case s' of
    ASort s | S.annSort s -> Left $ emptyG s
    ASort s -> Right $ emptyG s
    AnyAnnotation -> Left C.emptyC
    AnyEffect -> Right C.emptyC

solveIt :: M.Map Int (D.Set (Either A.Annotation E.Effect, Int)) -> State (D.Set (Either A.Annotation E.Effect, Int), M.Map Int (Either A.Annotation E.Effect)) ()
solveIt deps = do
  (worklist,analysis) <- get
  unless (D.size worklist == 0) $ do
    let (e',x) = D.elemAt 0 worklist
    e <- lookupExpr e'
    let (e1,e2) = (e,(\(Just w_1919) -> w_1919) $ M.lookup x analysis)
    let (analysis', isSubset) = case (e1,e2) of
          (Left a1, Left a2) | A.normalize (A.Union a1 a2) /= A.normalize a2 ->
            (M.insert x (Left $ A.Union a1 a2) analysis, False)
          (Left _, Left _) -> (analysis, True)
          (Right e1, Right e2) | E.normalize (E.Union e1 e2) /= E.normalize e2 ->
            (M.insert x (Right $ E.Union e1 e2) analysis, False)
          (Right _, Right _) -> (analysis, True)
          (a,b) -> error $ "Inconsistent annotations and effect mix: '" ++ show a ++ "' and '" ++ show b ++ "'"
    let worklist' = if isSubset
                    then D.deleteAt 0 worklist
                    else D.unions [D.deleteAt 0 worklist,fromMaybe D.empty $ M.lookup x deps]
    put (worklist',analysis')
    solveIt deps
  where
    lookupExpr e = do
      analysis <- use _2
      let (annAnalysis,_) = M.mapEither id analysis
      return $ case e of
        Left ann -> Left $ A.replaceFree annAnalysis ann
        Right eff -> Right $ E.replaceFree analysis eff

        -- Left (A.Var x) -> (\(Just w_1919) -> w_1919) $ M.lookup x analysis
        -- Left ex -> Left ex
        -- Right (E.Var x) -> (\(Just w_1919) -> w_1919) $ M.lookup x analysis
        -- Right (E.Flow l (A.Var x)) ->
        --   case (\(Just w_1919) -> w_1919) $ M.lookup x analysis of
        --     (Left v) -> Right $ E.Flow l v
        --     (Right e) -> error $ "Variable " ++ show x
        --                  ++ " was expected to be an annotation. Found effect"
        -- Right ex -> Right ex

-- solve :: (Functor m, Monad m) => [(Either A.Annotation E.Effect, Int)] -> [Int] -> Int -> Int -> StateT RContext m ()
solve c x b d = do
  analysis <- (\x y z -> M.fromList $ x ++ y ++ z)
              <$> mapM (analysisM . snd) c
              <*> (mapM analysisM $ [b,d])
              <*> mapM analysisC x
  deps <- return (foldl depsInit M.empty (map fst c))
              >>= return . (\s0 -> foldl depsExtend s0 c)
              
  let worklist = D.fromList c
      (_,res) = trace (show (deps,worklist,analysis)) execState (solveIt deps) (worklist,analysis)
  return $ case ((\(Just x) -> x) $ M.lookup b res, (\(Just x) -> x) $ M.lookup d res) of
    (Left ann, Right eff) -> (ann,eff)
    err -> error $ "Invalid result for solve: " ++ show err
  

  where
    analysisC v = do
      s' <- ((\(Just x) -> x) . M.lookup v) <$> use fvGammas
      return $ if isAnnConstraint s'
        then (v,Left $ A.Var v)
        else (v,Right $ E.Var v)
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
          
