module Analysis.Types.Render where
import Text.LaTeX.Packages.AMSMath
import Text.LaTeX.Base.Texy
import Text.LaTeX.Base
import Data.Text hiding (group)
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

quad :: LaTeXC l => l
quad = comm0 ";"

group e = raw (pack "{") <> e <> raw (pack "}")

appL :: LaTeXC l => l
appL = stexy "*"

xrightarrow l = comm1 "xrightarrow" l

renderFile f = R.renderFile f . mkLatex

mkLatex :: Texy l => l -> LaTeX
mkLatex l = (documentclass [] minimal) <> usepackage [] amsmath <> document (math $ texy l)

stexy s = texy $ (pack $ s :: Text)

typett :: LaTeXC l => l -> l
typett = mathtt

renderSort s =
  case s of
    S.Ann -> typett $ texy $ pack "A"
    S.Eff -> typett $ texy $ pack "E"
    S.Arr a1@(S.Arr _ _) a2 -> autoParens (renderSort a1) <> to <> renderSort a2
    S.Arr a1 a2 -> renderSort a1 <> to <> renderSort a2
    
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
    labelf _ l = return $ textbf $ stexy $ "@" ++ l
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
    arrf _ t1 eff t2 = return $ autoParens t1 <> xrightarrow (texy eff) <> t2
    alg :: LaTeXC l => At.Algebra Identity At.Type l
    alg = At.Algebra{
      At.ftbool = tboolf,
      At.fforall = forallf,
      At.fann = annf,
      At.farr = arrf
      }


instance Texy S.Sort where
  texy = renderSort

instance Texy A.Annotation where
  texy = renderAnn

instance Texy E.Effect where
  texy = renderEff

instance Texy At.Type where
  texy = renderAnnType

instance Texy e => Texy (D.Set e) where
  texy s
    | D.null s = autoBraces $ stexy ""
    | otherwise = autoBraces $ D.fold (\e s -> texy e <> stexy "," <> s) (texy $ D.elemAt 0 s) $ D.deleteAt 0 s
