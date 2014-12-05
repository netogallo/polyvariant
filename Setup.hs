{-# Language CPP #-}
import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo hiding (libdir)
import System.FilePath ((</>))
import System.Process

#ifdef ghcjs_HOST_OS
main = defaultMainWithHooks simpleUserHooks{
  postBuild = copyIndexFile
  }
#else
main = defaultMain
#endif

indexFileName = "index.html"

copyIndexFile _ _ desc lbi = do
  let
    PackageName name = pkgName $ package desc
    bDir = buildDir lbi </> name </> (name ++ ".jsexe")
    index = dataDir (localPkgDescr lbi) </> indexFileName
  _ <- createProcess $ proc "cp" [index,bDir </> indexFileName]
  return ()
