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
  castToHTMLInputElement,
  castToHTMLHeadingElement,
  castToHTMLParagraphElement,
  castToHTMLTableCellElement)
import GHCJS.DOM.HTMLInputElement (htmlInputElementGetValue,htmlInputElementGetChecked)
import GHCJS.DOM.Element (elementOnclick)
import Analysis.Types.LambdaCalc
import qualified Analysis.Types.Type as Ty
import Analysis.Types.Render
import Analysis.Algorithms.Common
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
import Safe (readMay)
import Control.Monad (unless)

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

effectsDivName = "effectsDiv"

compileName = "compileInput"

examplesName = "examplesDiv"

logName1 = "logDiv1"

logName2 = "logDiv2"

messagesName = "messages"

redCalcName = "redCalcRenderDiv"

doRedName = "performReduction"

examplesDiv = fmap castToHTMLDivElement . pageElement examplesName

compileInput = fmap castToHTMLInputElement . pageElement compileName

calcInput = fmap castToHTMLTextAreaElement . pageElement calcInputName

calcRender = fmap castToHTMLDivElement . pageElement calcRenderName

typeRender = fmap castToHTMLDivElement . pageElement typeRenderName

messagesDiv = fmap castToHTMLDivElement . pageElement messagesName

redCalcDiv = fmap castToHTMLDivElement . pageElement redCalcName

effectsDivSel = fmap castToHTMLDivElement . pageElement effectsDivName

doRedInputSel = fmap castToHTMLInputElement . pageElement doRedName

logDivs ui = mapM (\e -> fmap castToHTMLDivElement $ pageElement e ui) [logName1,logName2]

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

entryDivId i = "logEntry_" ++ show i

createEntryDiv i = do
  (Just doc) <- currentDocument
  (Just e) <- documentCreateElement doc ("div" :: String)
  elementSetAttribute e ("id" :: String) (entryDivId i)
  return e

createElement e = do
  (Just doc) <- currentDocument
  (Just e') <- documentCreateElement doc (e :: String)
  return e'

renderEntry e = do
  entry <- createEntryDiv $ logLabel e
  tbl <- createElement "table"
  h <- createElement "h4"
  elementSetAttribute tbl ("border" :: String) ("1" :: String)
  htmlElementSetInnerHTML (castToHTMLHeadingElement h) $ "Label @" ++ show (logLabel e)
  let cssClass = if logLabel e `mod` 2 == 0 then "logEven" else "logOdd"
  elementSetAttribute entry ("class" :: String) (cssClass :: String)
  nodeAppendChild entry (Just h)
  nodeAppendChild entry (Just tbl)
  let es = renderLog e
  mapM_ (\x -> renderRow x >>= nodeAppendChild tbl . Just >> return ()) es
  return entry
  where
    renderRow (e1,e2) = do
      r <- createElement "tr"
      c1 <- createElement "td"
      c2 <- createElement "td"
      let addContent e v = do
            htmlElementSetInnerHTML (castToHTMLTableCellElement e) $ T.unpack $ T.concat ["$$",render $ (texy v :: LaTeX),"$$"]
            nodeAppendChild r (Just e)
      addContent c1 e1
      addContent c2 e2
      return r

clearMessages webUi = do
  msgsDiv <- messagesDiv webUi
  htmlElementSetInnerHTML msgsDiv ("" :: String)

appendPlainMessage webUi msg = do
  msgsDiv <- messagesDiv webUi
  htmlElementSetInnerHTML msgsDiv msg

appendRawMessage webUi msg = do
  msgsDiv <- messagesDiv webUi
  _ <- nodeAppendChild msgsDiv (Just msg)
  return ()

appendMessage webUi msg = do
  (Just doc) <- currentDocument
  (Just e') <- documentCreateElement doc ("p" :: String)
  htmlElementSetInnerHTML (castToHTMLParagraphElement e') (msg :: String)
  appendRawMessage webUi e'

renderReduction webUi term = do
  redDiv <- redCalcDiv webUi
  doRed <- doRedInputSel webUi >>= htmlInputElementGetChecked
  unless (not doRed) $ do
    case reduceExpr term of
      (Left msg) -> appendMessage webUi msg
      (Right red) -> htmlElementSetInnerHTML redDiv $ T.unpack $ T.concat [
        "$$", R.render (texy red :: LaTeX), "$$"]

renderErrorMsgs (Failure i msg) =
  "<div>Error occured in expression labeled <b>@" ++ show i ++ "</b>:&nbsp;</div>"
  ++ (concat $ map (++" ") $ map (renderFailure f) msg)
  where
    rend e = T.unpack $ T.concat ["$$",R.render (texy e :: LaTeX),"$$"]
    f = (\x -> "<div>" ++ x ++ "</div>",rend,rend,rend,rend)

compile webUi = do
  calc <- readMay <$> (calcInput webUi >>= htmlTextAreaElementGetValue)
  calcDiv <- calcRender webUi
  typeDiv <- typeRender webUi
  effectsDiv <- effectsDivSel webUi
  clearMessages webUi
  logs <- logDivs webUi
  let result = calc >>= Just . reconstruction
      renderCtx ctx =
        mapM_ (\e -> do
                  el <- renderEntry e
                  mapM_ (\l -> renderEntry e >>= nodeAppendChild l . Just) logs
                  return ()) $ _history ctx
  case result of
    Just (Right (ty,eff),ctx) -> do
      htmlElementSetInnerHTML calcDiv $ T.unpack $ T.concat ["$$",R.render $ (texy ((\(Just w_1919) -> w_1919) calc) :: LaTeX),"$$"]
      htmlElementSetInnerHTML typeDiv $ T.unpack $ T.concat ["$$",R.render $ (texy ty :: LaTeX),"$$"]
      mapM_ (flip htmlElementSetInnerHTML ("" :: String)) logs
      renderCtx ctx
      htmlElementSetInnerHTML effectsDiv $ T.unpack $ T.concat [
        "$$",R.render (texy eff :: LaTeX),"$$"]
    Just (Left err,ctx) -> do
      htmlElementSetInnerHTML calcDiv $ T.unpack $ T.concat ["$$",R.render $ (texy ((\(Just w_1919) -> w_1919) calc) :: LaTeX),"$$"]
      appendPlainMessage webUi $ renderErrorMsgs err
      renderCtx ctx
    Nothing -> appendMessage webUi ("Could not parse (read) the given expression." :: String)
  case calc of
    Nothing -> return ()
    Just term' -> renderReduction webUi term'
  reRender

webMain = runWebGUI $ \webUi -> do
  b <- compileInput webUi
  elementOnclick b (lift $ compile webUi)
  mapM_ (addExample webUi) allExamples
  return ()
