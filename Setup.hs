{-# Language CPP #-}
#ifdef COMPGHC
import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo hiding (libdir)

main = defaultMainWithHooks simpleUserHooks

#else
import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.Simple.LocalBuildInfo hiding (libdir)
import System.FilePath ((</>))
import System.Process


main = defaultMainWithHooks simpleUserHooks{
  postBuild = copyIndexFile
  }

indexFileName = "index.html"

copyIndexFile _ _ desc lbi = do
  let
    PackageName name = pkgName $ package desc
    bDir = buildDir lbi </> name </> (name ++ ".jsexe")
    index = dataDir (localPkgDescr lbi) </> indexFileName
  _ <- createProcess $ proc "cp" [index,bDir </> indexFileName]
  return ()
#endif
