{-# Language OverloadedStrings, ForeignFunctionInterface, JavaScriptFFI #-}
module Analysis.Web.Dom where

import Control.Applicative ((<$>))
import GHCJS.DOM (
  runWebGUI,
  postGUISync,
  postGUIAsync,
  currentDocument,
  webViewGetDomDocument)
import GHCJS.DOM.Document (
  documentCreateElement, 
  documentGetElementById,
  documentGetBody)
import GHCJS.DOM.HTMLElement (
  htmlElementSetInnerText,
  htmlElementSetInnerHTML)
import GHCJS.DOM.Types(
  Node(..),
  castToHTMLElement,
  castToHTMLDivElement,
  castToHTMLInputElement)
import GHCJS.DOM.HTMLInputElement (htmlInputElementGetValue)
import GHCJS.DOM.Element (elementOnclick)
import Analysis.Types.LambdaCalc
import qualified Analysis.Types.Type as Ty
import Analysis.Types.Render
import Analysis.Algorithms.Reconstruction (reconstruction)
import qualified Data.Text as T
import Text.LaTeX.Base.Texy
import Control.Monad.Trans
import qualified Text.LaTeX.Base.Render as R
import Text.LaTeX.Base
import Debug.Trace
import Analysis.Examples
import GHCJS.DOM.Node
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLTextAreaElement
import GHCJS.DOM.Document

foreign import javascript unsafe "reRender()"
  reRender :: IO ()

a >?> b = do
  a' <- a
  case a' of
    Nothing -> return Nothing
    Just a'' -> b a''

pageElement name webUi = do
  c <- webViewGetDomDocument webUi
       >?> flip documentGetElementById name
  case c of
    Nothing -> fail $ "The dom element "
                     ++ name
                     ++ " is missing."
    Just e -> return e

calcInputName = "calcInput"

typeRenderName = "typeRenderDiv"

calcRenderName = "calcRenderDiv"

compileName = "compileInput"

examplesName = "examplesDiv"

examplesDiv = fmap castToHTMLDivElement . pageElement examplesName

compileInput = fmap castToHTMLInputElement . pageElement compileName

calcInput = fmap castToHTMLTextAreaElement . pageElement calcInputName

calcRender = fmap castToHTMLDivElement . pageElement calcRenderName

typeRender = fmap castToHTMLDivElement . pageElement typeRenderName

addExample webUi ex = do
  (Just doc) <- currentDocument
  (Just e') <- documentCreateElement doc ("input" :: String)
  let e =  castToHTMLInputElement e'
  exDiv <- examplesDiv webUi
  elementSetAttribute e ("value" :: String) ("Example" :: String)
  elementSetAttribute e ("type" :: String) ("submit" :: String)
  elementOnclick e $ lift $ do
    inputArea <- calcInput webUi
    htmlTextAreaElementSetValue inputArea (show ex)
  _ <- nodeAppendChild exDiv (Just e')
  return ()

compile webUi = do
  calc <- (\e -> read $ trace (show t1) e) <$> (calcInput webUi >>= htmlTextAreaElementGetValue)
  calcDiv <- calcRender webUi
  typeDiv <- typeRender webUi
  let (ty,_,_,_) = reconstruction calc
  htmlElementSetInnerHTML calcDiv $ T.unpack $ T.concat ["$$",R.render $ (texy calc :: LaTeX),"$$"]
  htmlElementSetInnerHTML typeDiv $ T.unpack $ T.concat ["$$",R.render $ (texy ty :: LaTeX),"$$"]
  reRender

webMain = runWebGUI $ \webUi -> do
  b <- compileInput webUi
  elementOnclick b (lift $ compile webUi)
  mapM_ (addExample webUi) allExamples
  return ()
