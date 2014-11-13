{-# Language ViewPatterns #-}
module Analysis.Algorithms.Match where

import Analysis.Types.AnnType
import qualified Data.Map as M
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S

getChis eff =
  let Just (expr,arg) = E.mApp eff
      x = case arg of
        Left (A.Var x') -> x'
        Right (E.Var x') -> x'
  in case expr of
    E.Var d0 -> (d0,[x])
    (E.mApp -> Just _) ->
      let (d0,xs) = getChis expr
      in (d0,xs ++ [x])

getBetas ann =
  let A.App fun arg = ann
      b = case arg of
        (A.Var b') -> b'
  in case fun of
    A.Var b0 -> (b0,[b])
    A.App _ _ ->
      let (b0,bs) = getBetas fun
      in (b0,bs++[b])


match sigma t1x t2x = do
  case (t1x,t2x) of
    (TBool,TBool) -> M.empty
    (Forall v1 t1,Forall v2 t2) | S.sort v1 == S.sort v2 -> match (M.insert (S.name v2) (S.sort v2) sigma) t1 t2
    (Arr t1 phi (Ann t2 psi2), Arr t1' (eff@(E.mApp -> Just (_,_))) (Ann t2' (bs@(A.App _ _)))) | t1 == t1' ->
      let (d0,xs') = getChis eff
          mkVar v = S.Var v $ (\(Just w_1919) -> w_1919) $ M.lookup v sigma
          xs = map mkVar xs'
          d0Rep = foldr (\v s -> E.Abs v s) phi xs
          (b0,bs') = getBetas bs
          betas = map mkVar bs'
          b0Rep = foldr (\v s -> A.Abs v s) psi2 betas
      in M.union (M.fromList [(d0,Right d0Rep),(b0,Left b0Rep)]) $ match sigma t2 t2'
        
    
  
