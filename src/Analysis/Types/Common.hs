{-# Language MultiParamTypeClasses, FunctionalDependencies #-}
module Analysis.Types.Common where
import qualified Data.Map as M
import qualified Analysis.Types.Sorts as S
import Data.Maybe
import Control.Monad.State

data Boundness = Bound | Free deriving (Show,Eq,Enum,Ord)

class LambdaCalculus a alg | a -> alg where
  lambdaDepths :: a -> M.Map Int Int
  byId :: Int -> a -> Maybe a
  foldM :: Monad m => alg m x -> a -> m x

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


subVar vcons rep i v = do
  let rep' = fromJust $ M.lookup i rep
  (n,freeVars) <- get
  case (M.lookup v rep', M.lookup v freeVars) of
    -- Free variables, replace them with a
    -- fresh name
    (Nothing,Nothing) -> do
      put (n-1, M.insert v n freeVars)
      return $ vcons n
    (Nothing,Just n') -> return $ vcons n'
    (Just n',_) -> return $ vcons n'

subAbs acons rep i v e =
  let rep' = fromJust $ M.lookup i rep
  in return $ acons v{S.name=fromJust $ M.lookup (S.name v) rep'} e
