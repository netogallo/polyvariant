{-# Language MultiParamTypeClasses, FunctionalDependencies, ViewPatterns, TypeFamilies, FlexibleContexts #-}
module Analysis.Types.Common where
import qualified Data.Map as M
import qualified Analysis.Types.Sorts as S
import Data.Maybe
import Control.Monad.State (put,get)
import qualified Data.Set as D
import Control.Monad.Identity (runIdentity)
import Control.Monad hiding (foldM,void)
import Control.Monad.State hiding (void,foldM)

data Boundness = Bound | Free deriving (Show,Eq,Enum,Ord)

data Variable t =
  Var {name :: Int, set :: t}
  deriving (Eq, Read, Show, Ord)

class Group a where
  void :: a
  (<+>) :: a -> a -> a

instance Ord a => Group (D.Set a) where
  void = D.empty
  (<+>) = D.union

instance Ord k => Group (M.Map k v) where
  void = M.empty
  (<+>) = M.union

class Fold a alg | a -> alg where
  byId :: Int -> a -> Maybe a
  foldM :: Monad m => alg m a x -> a -> m x
  baseAlgebra :: Monad m => alg m a a
  groupAlgebra :: (Monad m, Group g) => alg m a g

class Fold a alg => WithAbstraction a alg | a -> alg where
  abst :: a -> Maybe (S.FlowVariable,a)
  abstC :: S.FlowVariable -> a -> a
  increment :: Int -> a -> a
  baseAbstAlgebra :: (Monad m) => alg m a a -> (Int -> S.FlowVariable -> a -> m a) -> alg m a a
  groupAbstAlgebra :: (Group g, Monad m) => alg m a g -> (Int -> S.FlowVariable -> g -> m g) -> alg m a g
  lambdaDepths :: a -> M.Map Int Int
  vars :: a -> D.Set (Int,Boundness)

class WithAbstraction a alg => LambdaCalculus a alg | a -> alg where
  app :: a -> Maybe (a,a)
  appC :: a -> a -> a
  var :: a -> Maybe Int
  varC :: Int -> a
  baseCalcAlgebra :: Monad m => alg m a a -> (Int -> Int -> m a) -> (Int -> a -> a -> m a) -> alg m a a
  groupCalcAlgebra :: (Group g, Monad m) => alg m a g -> (Int -> Int -> m g)  -> (Int -> g -> g -> m g) -> alg m a g

class Fold a alg => WithSets a alg | a -> alg where
  unionM :: a -> Maybe (a,a)
  unionC :: a -> a -> a
  setM :: a -> Maybe (D.Set a)
  setC :: D.Set a -> a
  emptyM :: a -> Maybe ()
  emptyC :: a
  unionAlgebra :: (Monad m, Ord a) => alg m a a -> (Int -> a -> a -> m a) -> (Int -> m a) -> alg m a a
  groupUnionAlgebra :: (Monad m, Ord x) => alg m a x -> (Int -> x -> x -> m x) -> (Int -> m x) -> alg m a x

defAlgebra :: (Monad m, WithAbstraction a alg, LambdaCalculus a alg) => alg m a a
defAlgebra = baseCalcAlgebra (baseAbstAlgebra baseAlgebra baseAbst) baseVar baseApp

baseVar _ i = return $ varC i

baseAbst _ v a = return $ abstC v a

baseApp _ a1 a2 = return $ appC a1 a2

baseEmpty _ = return emptyC

defGroupAlgebra :: (Monad m, Group x, LambdaCalculus a alg) => alg m a x
defGroupAlgebra = groupCalcAlgebra (groupAbstAlgebra groupAlgebra baseGAbst) baseGVar baseGApp

baseGVar _ _ = return $ void

baseGAbst _ _ a = return a

baseGApp _ a b = return $ a <+> b

bound (_,b) = b == Bound

subVar vcons rep i v = do
  let rep' = fromJust $ M.lookup i rep
  (n,freeVars) <- get
  case (M.lookup v rep', M.lookup v freeVars) of
    -- Free variables, replace them with a
    -- fresh name
    (Just n',_) -> return $ vcons n'
    (Nothing,Nothing) -> do
      put (n-1, M.insert v n freeVars)
      return $ vcons n
    (Nothing,Just n') -> return $ vcons n'

subAbs acons rep i v e =
  let rep' = fromJust $ M.lookup i rep
  in return $ acons v{S.name=fromJust $ M.lookup (S.name v) rep'} e

mkRepBase base = M.map (\e -> (e,True)) base

baseRepAbstAlg base'' offset e = groupAbstAlgebra groupAlgebra abstF
  where
    d = M.map (+1) $ lambdaDepths e
    base = mkRepBase base''
    insertIfIsBase (rep1,b1) (rep2,b2)
      -- Check if the replacement is from the base set of
      -- replacements. In such a case, the replacement
      -- should be preformed since there is a bounder
      -- for the variable
      | b2 = (rep1,b1)
      | otherwise = (rep2,b2)
    abstF i v reps =
      let
        name = offset + (fromJust $ M.lookup i d)
        -- If a replacement is already there, leave it since
        -- it must be bound by a deeper lambda
        m' = M.map (M.insertWith insertIfIsBase (S.name v) (name,False)) reps
        base' = M.insert (S.name v) (name,False) base
      in return $ M.insert i base' $ m'

baseRepAlg base'' offset e = groupCalcAlgebra (baseRepAbstAlg base'' offset e) varF appF
  where
    d = M.map (+1) $ lambdaDepths e
    base = mkRepBase base''
    varF i _ = return $ M.fromList [(i,base)]
    appF i ma mb = return $ M.insert i base $ M.union ma mb

mkGetVar rep i v =  M.lookup v $ fromJust $ M.lookup i rep

baseSubAbstAlg rep = baseAbstAlgebra baseAlgebra abstF
  where
    getVar i v = mkGetVar rep i v
    abstF i var e = return $ abstC var{S.name=fromJust $ getVar i (S.name var)} e

baseSubAlg :: (LambdaCalculus a alg, Monad m) => M.Map Int (M.Map Int Int) -> alg m a a
baseSubAlg rep = baseCalcAlgebra (baseSubAbstAlg rep) varF appF
  where
    getVar i v = mkGetVar rep i v
    varF i v = 
      return $ case (getVar i v) of
        Nothing | v < 0 -> varC v
        Just i' -> varC i'
        _ -> error $ "Free variables must have a negative identifier, found: " ++ show i
    appF _ a1 a2 = return $ appC a1 a2

baseUnionRepAlg base' offset e = groupUnionAlgebra (baseRepAlg base' offset e) unionF emptyF
  where
    base = M.map (\e -> (e,True)) base'
    unionF i ma mb = return $ M.insert i base $ M.union ma mb
    emptyF i = return $ M.fromList [(i,base)]

mkCalcAlgebra varF abstF appF = baseCalcAlgebra (baseAbstAlgebra baseAlgebra abstF) varF appF
mkGroupCalcAlgebra varF abstF appF = groupCalcAlgebra (groupAbstAlgebra groupAlgebra abstF) varF appF

boundedVarsAlg :: (Monad m, WithAbstraction a alg) => alg m a (M.Map Int (D.Set Int))
boundedVarsAlg = groupAbstAlgebra groupAlgebra abstF
  where
    abstF i v s = return $ M.map (D.insert $ S.name v) $ M.insert i D.empty s
    
boundedVarsCalcAlg :: (Monad m, LambdaCalculus a alg) => alg m a (M.Map Int (D.Set Int))
boundedVarsCalcAlg = groupCalcAlgebra (boundedVarsAlg) varF appF
  where
    varF i _ = return $ M.fromList [(i,D.empty)]
    appF i a1 a2 = return $ M.insert i D.empty $ M.union a1 a2

getBoundVars :: (LambdaCalculus a alg) => a -> M.Map Int (D.Set Int)
getBoundVars = runIdentity . foldM boundedVarsCalcAlg

boundedVarsSetAlg :: (Monad m,LambdaCalculus a alg, WithSets a alg) => alg m a (M.Map Int (D.Set Int))
boundedVarsSetAlg = groupUnionAlgebra boundedVarsCalcAlg unionF emptyF
  where
    unionF i a1 a2 = return $ M.insert i D.empty $ M.union a1 a2
    emptyF i = return $ M.fromList [(i,D.empty)]

allShadowedBaseAlg :: (LambdaCalculus a alg, Monad m) => alg m a (M.Map Int (Int,Bool))
allShadowedBaseAlg = mkGroupCalcAlgebra varF abstF baseGApp
  where
    varF i v = return $ M.fromList [(i,(v,False))]
    abstF _ v s = return $ M.map (\val@(v',_) -> if S.name v == v' then (S.name v,True) else val) s
    
shadows v arg = runIdentity $ do
  ss <- foldM allShadowedBaseAlg arg
  return $ M.foldWithKey (\k (v',isShadowed) s -> if v == v' then M.insert k isShadowed s else s) M.empty ss

shadowsBaseAlg v = mkGroupCalcAlgebra varF abstF appF
  where
    appF _ s1 s2 = return $ M.union s1 s2
    varF i v'
      | v == v' = return $ M.fromList [(i,False)]
      | otherwise = return M.empty
    abstF i v' s
      | S.name v' == v = return $ M.map (const True) s
      | otherwise = return s

-- Algebra to replace the given free variables
baseReplaceAlg rep elm = alg
  where
    boundVars i = (\(Just w_1919) -> w_1919) $ M.lookup i $ getBoundVars elm
    isBound i v = D.member v $ boundVars i
    varf i v =
      case M.lookup v rep of
        Nothing -> return $ varC v
        _ | isBound i v -> return $ varC v
        Just new -> return new
    alg = mkCalcAlgebra varf baseAbst baseApp

baseAppAlg :: (Fold a alg,LambdaCalculus a alg, Monad m) => a -> a -> alg m a a
baseAppAlg (abst -> Just (var,a1)) a2 = alg $ lambdaDepths a1
  where
    shadowedVars = shadows (S.name var) a1
    a2' = increment 1 a2
    fvar depths i v
      | S.name var == v =
        let d = M.lookup i depths
            isShadowed = fromJust $ M.lookup i shadowedVars
        in case d of
          _ | isShadowed -> return $ varC v
          -- One has to be added to the depth because at the
          -- end of the application, the bound variables in
          -- the term will be subtracted 1
          Just d' | d' > 0 -> return $ increment (d' + 1) a2'
          Just _ -> return a2'
          Nothing -> fail "No depth for expression!"
      | otherwise = return $ varC v
    alg depths = mkCalcAlgebra (fvar depths) baseAbst baseApp
baseAppAlg _ _ = defAlgebra

-- | Algebra to increase/decrease by i the index of the provided variables
baseIncAlg i vars = (alg vars)
  where
    fvar vars _ v
      | D.member v vars = return $ varC $ v + i
      | otherwise = return $ varC v
    fabs vars _ v s
      | D.member (S.name v) vars = return $ abstC v{S.name = i + S.name v} s
      | otherwise = return $ abstC v s
    alg vars = mkCalcAlgebra (fvar vars) (fabs vars) baseApp

-- | Algebra to list all the variables of an expression
baseVarsAlg :: (Monad m, LambdaCalculus a alg) => alg m a (D.Set (Int,Boundness))
baseVarsAlg = mkGroupCalcAlgebra var abst app
  where
    var _ v = return (D.singleton (v,Free))
    abst _ v s = do
      let bounder (v',boundness)
            | S.name v == v' = (v',Bound)
            | otherwise = (v',boundness)
      return $ D.insert (S.name v, Bound) . D.map bounder $ s
    app _ a1 a2 = return $ D.union a1 a2


baseRedUnionAlg :: (LambdaCalculus a alg, Monad m, Ord a, WithSets a alg) => alg m a a
baseRedUnionAlg = mkCalcAlgebra baseVar baseAbst appF
  where
    appF' _ a1 a2 = return $ appC a1 a2
    appF _ a1 a2 =
      return $ case (a1,a2) of
        (unionM -> Just (a11,a12),_) -> unionC (appC a11 a2) (appC a12 a2)
        (abst -> Just (v1,f1),abst -> Just (v2,f2)) | v1 == v2 -> abstC v1 $ unionC f1 f2
        _ -> appC a1 a2

unions :: (Fold a alg, WithSets a alg, Ord a) => a -> a
unions = runIdentity . foldM alg
  where
    unionF _ a1 a2 =
      return $ case (a1,a2) of
        (setM -> Just s1,setM -> Just s2) -> setC $ D.union s1 s2
        
        (emptyM -> Just (), emptyM -> Just ()) -> setC $ D.empty
        
        (setM -> Just s1,emptyM -> Just ()) -> setC s1
        (emptyM -> Just (), setM -> Just s2) -> setC s2

        (a1', emptyM -> Just ()) -> setC $ D.singleton a1'
        (emptyM -> Just (), a2') -> setC $ D.singleton a2'
        
        (setM -> Just s1, a2') -> setC $ D.insert a2' s1
        (a1', setM -> Just s2) -> setC $ D.insert a1' s2

        (a1',a2') -> setC $ D.fromList [a1',a2']
    emptyF _ = return $ setC D.empty
    alg = unionAlgebra baseAlgebra unionF emptyF

byIdDual c i' i a1 a2 = do
  unless (i /= i') $ put $ Just $ c a1 a2
  return $ c a1 a2

byIdAlgebra i = mkCalcAlgebra varF abstF appF
  where
    varF i' v = do
      unless (i' /= i) $ put (Just (varC v))
      return $ varC v
    abstF i' v e = do
      unless (i /= i') $ put (Just (abstC v e))
      return $ abstC v e
    appF i' a1 a2 = byIdDual appC i' i a1 a2

byIdSetAlgebra :: (LambdaCalculus a alg, MonadState (Maybe a) m, Ord a, WithSets a alg) => Int -> alg m a a
byIdSetAlgebra i = unionAlgebra (byIdAlgebra i) unF emptyF
  where
    unF i' a1 a2 = byIdDual unionC i' i a1 a2
    emptyF i' = do
      unless (i /= i') $ put (Just emptyC)
      return emptyC
