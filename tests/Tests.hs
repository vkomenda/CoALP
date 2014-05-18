-- |
-- * Top-level module for all tests

module Main where

import qualified CoALP.Tests.Unit.Subst  as Subst
import qualified CoALP.Tests.Unit.Guards as Guards

import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "Unit tests"
  [
    Subst.tests
  , Guards.tests
  ]
