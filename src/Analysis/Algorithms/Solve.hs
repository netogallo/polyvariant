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

solveIt :: M.Map Int (D.Set (Either A.Annotation E.Effect, Int)) -> State (D.Set (Either A.Annotation E.Effect, Int), M.Map Int (Either A.Annotation E.Effect)) ()
solveIt deps = do
  (worklist,analysis) <- get
  unless (D.size worklist == 0) $ do
    let (e,x) = D.elemAt 0 worklist
    let (analysis', isSubset) = case (e,fromJust $ M.lookup x analysis) of
          (Left a1, Left a2) | A.normalize (A.Union a1 a2) /= A.normalize a2 ->
            (M.insert x (Left $ A.Union a1 a2) analysis, False)
          (Left _, Left _) -> (analysis, True)
          (Right e1, Right e2) | E.normalize (E.Union e1 e2) /= E.normalize e2 ->
            (M.insert x (Right $ E.Union e1 e2) analysis, False)
          (Right _, Right _) -> (analysis, True)
          (a,b) -> error $ "Inconsistent annotations and effect mix: '" ++ show a ++ "' and '" ++ show b ++ "'"
    let worklist' = if isSubset
                    then D.deleteAt 0 worklist
                    else D.unions [D.deleteAt 0 worklist,fromJust $ M.lookup x deps]
    put (worklist',analysis')
    solveIt deps

-- solve :: (Functor m, Monad m) => [(Either A.Annotation E.Effect, Int)] -> [Int] -> Int -> Int -> StateT RContext m ()
solve c x b d = do
  analysis <- (\x y z -> M.unions $ x ++ y ++ z)
              <$> mapM (analysisM . snd) c
              <*> (mapM analysisM $ [b,d])
              <*> mapM analysisC x
  deps <- return (foldl depsInit M.empty (map fst c))
              >>= return . (\s0 -> foldl depsExtend s0 c)
              
  let worklist = D.fromList c
      (_,res) = execState (solveIt deps) (worklist,analysis)
  return $ case (fromJust $ M.lookup b res, fromJust $ M.lookup d res) of
    (Left ann, Right eff) -> (ann,eff)
    err -> error $ "Invalid result for solve: " ++ show err
  

  where
    analysisC v = do
      s' <- (fromJust . M.lookup v) <$> use fvGammas
      return $ M.fromList $ (:[]) $ if isAnnConstraint s'
        then (v,Left $ A.Var v)
        else (v,Right $ E.Var v)
    analysisM v = do
      s' <- (fromJust . M.lookup v) <$> use fvGammas
      return $ M.fromList $ (:[]) $ case trace ("Analyisi lookup: " ++ show s') s' of
        ASort s@(S.Arr s1 _) | S.annSort s ->
          (v,Left $ A.Abs (S.Var v s1) A.Empty)
        ASort (S.Arr s1 _) ->
          (v,Right $ E.Abs (S.Var v s1) E.Empty)
        ASort S.Ann -> (v,Left $ A.Empty)
        ASort S.Eff -> (v,Right $ E.Empty)
        AnyAnnotation -> (v,Left $ A.Empty)
        AnyEffect -> (v,Right $ E.Empty)

    freeVars expr' =
      let vars expr = map fst $ filter (not . C.bound) $ D.toList $ C.vars expr
      in case expr' of
        Right e -> vars e
        Left e -> vars e
    depsInit :: M.Map Int (D.Set (Either A.Annotation E.Effect,Int)) -> Either A.Annotation E.Effect -> M.Map Int (D.Set (Either A.Annotation E.Effect,Int))
    depsInit deps expr = foldl (\s v -> M.insert v D.empty s) deps $ freeVars expr
    depsExtend :: M.Map Int (D.Set (Either A.Annotation E.Effect,Int)) -> (Either A.Annotation E.Effect,Int) -> M.Map Int (D.Set (Either A.Annotation E.Effect,Int))
    depsExtend deps c'@(expr,_) = foldl (\s v -> M.insertWith D.union v (D.singleton c') s) deps $ freeVars expr
          
