module Analysis.Common where

import Text.LaTeX.Packages.AMSMath
import Text.LaTeX.Base.Texy
import Text.LaTeX.Base
import Data.Text hiding (group,map,groupBy,zip,foldl1,replicate,foldl)
import Text.LaTeX.Base.Class
import qualified Text.LaTeX.Base.Render as R
import qualified Data.Set as D
import qualified Data.Map as M

stexy s = texy $ (pack $ s :: Text)

typett :: LaTeXC l => l -> l
typett = mathtt
renderFile f = R.renderFile f . mkLatex

mkLatex :: Texy l => l -> LaTeX
mkLatex l = (documentclass [] minimal) <> usepackage [] amsmath <> document (math $ texy l)

quad :: LaTeXC l => l
quad = comm0 ";"

group e = raw (pack "{") <> e <> raw (pack "}")

appL :: LaTeXC l => l
appL = stexy "*"

xrightarrow l = comm1 "xrightarrow" l

bar e = comm1 "bar" e

instance Texy e => Texy (D.Set e) where
  texy s
    | D.null s = autoBraces $ stexy ""
    | otherwise = autoBraces $ D.fold (\e s -> texy e <> stexy ";" <> quad <> s) (texy $ D.elemAt 0 s) $ D.deleteAt 0 s

instance (Texy l,Texy r) => Texy (Either l r) where
  texy e =
    case e of
      Left e' -> texy e'
      Right e' -> texy e'

instance (Texy k,Texy v) => Texy (M.Map k v) where
  texy m =
    texy $ M.foldWithKey (\k e s -> (texy k <> to <> texy e :: LaTeX) : s) [] m

renderLbl l = textbf $ stexy $ "@" ++ l
