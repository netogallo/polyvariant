{-# Language MultiParamTypeClasses, FunctionalDependencies, ViewPatterns #-}
module Analysis.Types.Common where
import qualified Data.Map as M
import qualified Analysis.Types.Sorts as S
import Data.Maybe
import Control.Monad.State (put,get,modify,StateT)
import qualified Data.Set as D
import Control.Monad.Identity (runIdentity)

data Boundness = Bound | Free deriving (Show,Eq,Enum,Ord)

data Variable t =
  Var {name :: String, set :: t}
  deriving (Eq, Read, Show, Ord)

class Group a where
  void :: a
  (<+>) :: a -> a -> a

instance Ord a => Group (D.Set a) where
  void = D.empty
  (<+>) = D.union

class Fold a alg | a -> alg where
  byId :: Int -> a -> Maybe a
  foldM :: Monad m => alg m a x -> a -> m x

class LambdaCalculus a alg | a -> alg where
  lambdaDepths :: a -> M.Map Int Int
  app :: a -> Maybe (a,a)
  appC :: a -> a -> a
  var :: a -> Maybe Int
  varC :: Int -> a
  abst :: a -> Maybe (S.FlowVariable,a)
  abstC :: S.FlowVariable -> a -> a
  increment :: Int -> a -> a
  baseAlgebra :: Monad m => (Int -> Int -> m a) -> (Int -> S.FlowVariable -> a -> m a) -> (Int -> a -> a -> m a) -> alg m a a
  groupAlgebra :: (Group g, Monad m) => (Int -> Int -> m g) -> (Int -> S.FlowVariable -> g -> m g) -> (Int -> g -> g -> m g) -> alg m a g
  vars :: a -> D.Set (Int,Boundness)

class LambdaCalculus a alg => WithSets a alg | a -> alg where
  unionM :: a -> Maybe (a,a)
  unionC :: a -> a -> a
  setM :: a -> Maybe (D.Set a)
  setC :: D.Set a -> a
  emptyM :: a -> Maybe ()
  emptyC :: a
  unionAlgebra :: (Monad m, Ord a) => alg m a a -> (Int -> a -> a -> m a) -> (Int -> m a) -> alg m a a
  groupUnionAlgebra :: (Monad m, Ord x) => alg m a x -> (Int -> x -> x -> m x) -> (Int -> m x) -> alg m a x

defAlgebra :: (Monad m, LambdaCalculus a alg) => alg m a a
defAlgebra = baseAlgebra baseVar baseAbst baseApp

baseVar _ i = return $ varC i

baseAbst _ v a = return $ abstC v a

baseApp _ a1 a2 = return $ appC a1 a2

defGroupAlgebra :: (Monad m, Group x, LambdaCalculus a alg) => alg m a x
defGroupAlgebra = groupAlgebra baseGVar baseGAbst baseGApp

baseGVar _ _ = return $ void

baseGAbst _ _ a = return a

baseGApp _ a b = return $ a <+> b

discard f = \x -> \_ -> f x

rename base i = return $ M.insert i base M.empty

rename1 base i s = return $ M.insert i base s

rename2 base i s1 s2 = return $ M.insert i base $ M.union s1 s2

renameAbs base offset obj i v s =
  let
    d = 1 + offset + (fromJust $ M.lookup i $ lambdaDepths obj)
    -- If a replacement is already 2defined for the variable, leave it that way
    -- since this variable must habe been bound earlier
  in return $ M.map (M.insertWith (\_ d' -> d') (S.name v) d) $ M.insert i base s

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

baseAppAlg (abst -> Just (var,a1)) a2 = alg $ lambdaDepths a1
  where
    a2' = increment 1 a2
    fvar depths i v
      | S.name var == v =
        let d = M.lookup i depths
        in case d of
          Just d' | d' > 0 -> return $ increment d' a2'
          Just _ -> return a2'
          Nothing -> fail "No depth for expression!"
      | otherwise = return $ varC v
    alg depths = baseAlgebra (fvar depths) baseAbst baseApp
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
    alg vars = baseAlgebra (fvar vars) (fabs vars) baseApp

-- | Algebra to list all the variables of an expression
baseVarsAlg :: (Monad m, LambdaCalculus a alg) => alg m a (D.Set (Int,Boundness))
baseVarsAlg = groupAlgebra var abst app
  where
    var _ v = return (D.singleton (v,Free))
    abst _ v s = do
      let bounder (v',boundness)
            | S.name v == v' = (v',Bound)
            | otherwise = (v',boundness)
      return $ D.insert (S.name v, Bound) . D.map bounder $ s
    app _ a1 a2 = return $ D.union a1 a2


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
    alg = unionAlgebra defAlgebra unionF emptyF

