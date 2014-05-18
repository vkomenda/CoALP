-- |
-- * Unit tests for guardedness

module CoALP.Tests.Unit.Guards
       (
         tests
       )
       where

import CoALP
import CoALP.UI

import Data.List
import Control.Applicative
--import Control.Concurrent
import Test.Tasty
import Test.Tasty.HUnit
import System.Directory
import System.IO.Unsafe

logicExt :: String
logicExt = ".logic"

-- FIXME: The relative path works only from the root of the source tree where
-- the .cabal file is located. Consider adding a command-line option to the test
-- executable to pass the directory with programs.
programsDir :: FilePath
programsDir = "programs"

programsGuarded :: FilePath
programsGuarded = programsDir ++ "/guarded"

programsUnguarded1 :: FilePath
programsUnguarded1 = programsDir ++ "/unguarded/Check1"

programsUnguarded2 :: FilePath
programsUnguarded2 = programsDir ++ "/unguarded/Check2"

programsUnguarded3 :: FilePath
programsUnguarded3 = programsDir ++ "/unguarded/Check3"

onFile :: (Program1 -> Bool) -> FilePath -> TestTree
onFile prop file = testCase file $ do
  (cls, _, _) <- parseItemsFile file
  prop (Pr cls) @?= True

{-# NOINLINE testOnFiles #-}
testOnFiles :: String -> (Program1 -> Bool) -> IO [FilePath] -> TestTree
testOnFiles name prop filesIO =
  testGroup name $ onFile prop <$> unsafePerformIO filesIO

{-# NOINLINE logicInDir #-}
logicInDir :: FilePath -> IO [FilePath]
logicInDir dir =
  getDirectoryContents dir >>=
  return . map ((++) (dir ++ "/")) . filter (isSuffixOf logicExt)

tests :: TestTree
tests =
  testGroup "Guardedness"
  [
    testOnFiles "Guarded programs pass the guardedness checks"
                guarded                $ logicInDir programsGuarded
  , testOnFiles "Programs unguarded in check 1 fail check 1"
                (not . guardedClauses) $ logicInDir programsUnguarded1
  , testOnFiles "Programs unguarded in check 2 pass check 1"
                guardedClauses         $ logicInDir programsUnguarded2
  , testOnFiles "Programs unguarded in check 2 fail check 2"
                (not . guardedMatches) $ logicInDir programsUnguarded2
  , testOnFiles "Programs unguarded in check 3 pass check 1"
                guardedClauses         $ logicInDir programsUnguarded3
  , testOnFiles "Programs unguarded in check 3 pass check 2"
                guardedMatches         $ logicInDir programsUnguarded3
  , testOnFiles "Programs unguarded in check 3 fail check 3"
                (not . guardedMgus)    $ logicInDir programsUnguarded3
  ]
