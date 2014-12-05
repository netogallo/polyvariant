{-# Language CPP #-}
module Main where

#ifdef COMPGHC
import Analysis.Algorithms.Reconstruction
import Analysis.Examples
main = error "This program only works with GHCJS"
#else
import Analysis.Web.Dom (webMain)
main = webMain
#endif
