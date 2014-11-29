{-# Language CPP #-}
module Main where

#ifdef COMPGHC
import Analysis.Algorithms.Reconstruction
import Analysis.Examples
import Analysis.Types.Tests
main = undefined
#else
import Analysis.Web.Dom (webMain)
main = webMain
#endif
