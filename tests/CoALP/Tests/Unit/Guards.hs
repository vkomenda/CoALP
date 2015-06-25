-- |
-- * Unit tests for guardedness

module CoALP.Tests.Unit.Guards
       (
         tests
       )
       where

import CoALP
import CoALP.UI

import qualified Data.Array as Array
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
  (cls, _) <- parseItemsFile file
  prop (Program $ Array.listArray (0, length cls - 1) cls) @?= True

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
    testOnFiles "Programs unguarded in tier 2 check fail it"
                (not . guardedMatch)      $ logicInDir programsUnguarded2
  , testOnFiles "Programs unguarded in tier 2 check fail tier 3 check"
                (not . guardedResolution) $ logicInDir programsUnguarded2
  , testOnFiles "Programs unguarded in tier 3 check pass tier 2 check"
                guardedMatch              $ logicInDir programsUnguarded3
  , testOnFiles "Programs unguarded in tier 3 check fail it"
                (not . guardedResolution) $ logicInDir programsUnguarded3
  , testOnFiles "Guarded programs pass tier 2 check"
                guardedMatch              $ logicInDir programsGuarded
  , testOnFiles "Guarded programs pass tier 3 check"
                guardedResolution         $ logicInDir programsGuarded
  ]
