{-# Language ScopedTypeVariables #-}
module Analysis.Types.Render where
import Analysis.Common
import Text.LaTeX.Packages.AMSMath
import Text.LaTeX.Base.Texy
import Text.LaTeX.Base
import Data.Text hiding (group,map,groupBy,zip,foldl1,replicate)
import qualified Analysis.Types.Annotation as A
import qualified Analysis.Types.Sorts as S
import Control.Monad.Identity
import Text.LaTeX.Base.Class
import qualified Text.LaTeX.Base.Render as R
import qualified Analysis.Types.Effect as E
import qualified Analysis.Types.AnnType as At
import qualified Analysis.Types.Common as C
import qualified Data.Map as M
import qualified Data.Set as D
import Data.List
import qualified Analysis.Types.LambdaCalc as L
import qualified Analysis.Types.Type as Ty

concatWith :: [a] -> [[a]] -> [a]
concatWith c [] = []
concatWith c xs@(_:_) = Data.List.tail $ Data.List.foldl (\x s -> x ++ c ++ s) [] xs

sexyset :: forall l t .(LaTeXC l,Texy t) => Int -> D.Set t -> l
sexyset n xs' =
  let xs = D.toList xs'
      groups :: [[t]]
      groups = map (map snd) . groupBy grp . sortBy srt $ zip [1..] xs
      grp a b = (fst a :: Int) `mod` n == (fst b :: Int) `mod` n
      srt a b = compare (fst a `mod` n) (fst b `mod` n)
      dims = concatWith " " $ replicate n "c"
      join e [] = mempty
      join e [x] = x
      join e xs = foldl1 (\a b -> a `e` b) xs
      render1 :: [LaTeX]
      render1 = map (join (&) . map texy) groups
      render2 = unpack $ render $ (join (\a b -> a <> lnbk <> b) render1 :: LaTeX)
  in autoBraces $ raw . pack $ "\\begin{array}{"++dims++"}"++render2++"\\end{array}"

renderSort s =
  case s of
    S.Ann -> typett $ texy $ pack "A"
    S.Eff -> typett $ texy $ pack "E"
    S.Arr a1@(S.Arr _ _) a2 -> autoParens (renderSort a1) <> to <> renderSort a2
    S.Arr a1 a2 -> renderSort a1 <> to <> renderSort a2

renderType t =
  case t of
    Ty.TBool -> (typett $ texy $ pack "B")
    Ty.Arr t1@(Ty.Arr _ _) t2 -> autoParens (renderType t1) <> to <> renderType t2
    Ty.Arr t1 t2 -> renderType t1 <> to <> renderType t2

renderAnn :: LaTeXC l => A.Annotation -> l
renderAnn ann = runIdentity $ A.foldAnnM alg ann
  where
    varf :: LaTeXC l => Int -> Int -> Identity l
    varf _ v = return $ beta ^: texy v
    absf _ (S.Var v s) b = return $ lambda
                           <> beta ^: texy v
                           <> stexy ":"
                           <> renderSort s
                           <> quad <> stexy "." <> quad <> b
    appf _ a1 a2 = return $ a1 <> appL <> a2
    labelf _ l = return $ renderLbl l
    unionf :: LaTeXC l => Int -> l -> l -> Identity l
    unionf i _ _ =
      let A.Set s = C.unions $ (\(Just x) -> x) $ C.byId i ann
      in return $ texy s
    emptyf _ = return $ autoBraces $ texy $ pack ""
    alg :: LaTeXC l => A.Algebra Identity A.Annotation l
    alg = A.Algebra{
      A.fvar = varf,
      A.fabs = absf,
      A.fapp = appf,
      A.flabel = labelf,
      A.funion = unionf,
      A.fempty = emptyf
    }

renderEff :: LaTeXC l => E.Effect -> l
renderEff elm = runIdentity $ E.foldEffectM alg elm
  where
    varf _ v = return $ delta ^: texy v
    appf _ a1 a2 = return $ a1 <> appL <> a2
    appAnnf _ eff ann = return $ eff <> appL <> texy ann
    absf _ v b =
      let var | S.annSort $ S.sort v = beta ^: (texy $ S.name v)
              | otherwise = delta ^: (texy $ S.name v)
      in return $ lambda <> var <> (stexy ":")
         <> texy (S.sort v) <> quad <> (stexy ".") <> quad <> b
    unionf i _ _ =
      let (E.Set s) = C.unions $ (\(Just x) -> x) $ C.byId i elm
      in return $ texy s
    flowf _ l ann = return $ autoParens $ (textbf $ stexy $ "@" ++ l) <> stexy "," <> texy ann
    emptyf _ = return $ autoBraces $ texy $ pack ""
    alg = E.Algebra {
      E.fvar = varf,
      E.fapp = appf,
      E.fappAnn = appAnnf,
      E.fabs = absf,
      E.funion = unionf,
      E.fflow = flowf,
      E.fempty = emptyf
      }

renderAnnType :: LaTeXC l => At.Type -> l
renderAnnType = runIdentity . At.foldTypeM alg
  where
    tboolf _ = return $ (typett $ texy $ pack "B")
    forallf _ fv t =
      let v | S.annSort $ S.sort fv = beta ^: (texy $ S.name fv)
            | otherwise = delta ^: (texy $ S.name fv)
      in return $ forall <> v <> stexy ":"
         <> texy (S.sort fv) <> quad <> stexy "." <> quad
         <> t
    annf _ t ann = return $ autoParens t ^: (texy ann)
    arrf _ t1 eff' t2 =
      let eff = case eff' of
            E.Set s -> texy s -- sexyset 1 s
            _ -> texy eff'
      in return $ autoParens t1 <> xrightarrow eff <> t2
    alg :: LaTeXC l => At.Algebra Identity At.Type l
    alg = At.Algebra{
      At.ftbool = tboolf,
      At.fforall = forallf,
      At.fann = annf,
      At.farr = arrf
      }

renderLambdaCalc :: (LaTeXC l, Texy t) => (L.LambdaCalc t) -> l
renderLambdaCalc expr = runIdentity $ L.foldLambdaCalcM alg expr
  where
    label i l = autoParens l ^: mathit (stexy $ "@" ++ show i)
    var v = stexy "x" ^: stexy (show v)
    varF i v = return $ var v
    bool b i = return $ label i $ mathbf $ stexy b
    vfalseF :: LaTeXC l => Int -> Identity l
    vfalseF = bool "False"
    vtrueF :: LaTeXC l => Int -> Identity l
    vtrueF = bool "True"
    absF i (C.Var v s) e =
      return $ label i $
        lambda <> var v <> stexy ":"
        <> texy s <> quad <> stexy "."
        <> quad <> e
    ifF i cond yes no = return $ label i $
      mathbf (stexy "if") <> quad <> cond
      <> quad <> mathbf (stexy "then") <> quad <> yes
      <> quad <> mathbf (stexy "else") <> quad <> no
    appF i a1 a2 = return $ label i $ a1 <> appL <> a2
    fixF i a1 = return $ mathbf (stexy "fix") <> quad <> a1
    alg :: (LaTeXC l,Texy t) => L.Algebra t Identity (L.LambdaCalc t) l
    alg = L.Algebra{
      L.fvar = varF,
      L.fvfalse = vfalseF,
      L.fvtrue = vtrueF,
      L.fabs = absF,
      L.fif = ifF,
      L.fapp = appF,
      L.ffix = fixF
      }

instance Texy Ty.Type where
  texy = renderType

instance Texy t => Texy (L.LambdaCalc t) where
  texy = renderLambdaCalc

instance Texy S.Sort where
  texy = renderSort

instance Texy A.Annotation where
  texy = renderAnn

instance Texy E.Effect where
  texy = renderEff

instance Texy At.Type where
  texy = renderAnnType
