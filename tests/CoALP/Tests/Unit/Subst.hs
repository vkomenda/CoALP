-- |
-- * Unit tests for substitution

module CoALP.Tests.Unit.Subst where

import CoALP
import CoALP.UI ()

import Test.Tasty
import Test.Tasty.HUnit

v0 :: Int
v0 = 0
v1 :: Int
v1 = 1
v2 :: Int
v2 = 2
--v100 :: Int
--v100 = 100

--g0 :: Goal
--g0 = Go [Fun "bit" [Fun "0" []]]

--gx :: Goal
--gx = Go [Fun "bit" [Var v100]]

--g1 :: Goal
--g1 = [Con "btree" :@: (Con "tree" :@: Var v100 :@: Con "0" :@: Con "empty")]

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "Term and atom MGUs"
  [
    testCase "A variable against a constant" $
      vv0 `mguMaybe` c0 @?= Just s0
  , testCase "A constant against a variable" $
      c0 `mguMaybe` vv0 @?= Just s0
  , testCase "A variable against a constant, inside of an atom" $
      (bit vv0) `mguMaybe` (bit c0) @?= Just s0
  ]
{-  , testGroup "Leaf substitutions"
    [
      testCase "Leaf substitutions of a ground tree is the empty list" $
        leafSubsts p (initialTree len g0) @?= []
    , testCase "Non-trivial leaf substitutions of a tree containing a variable" $
        leafSubsts p (initialTree len g1)
          @?= [LfS (Subst (Map.fromList
                           [
                             (v1, c0)
                           , (v2, cempty)
                           , (v100, vv0)
                           ]))
                   [3]]
    ]  -}
{-   , testGroup "Short derivations"
    [
      testCase "An immediate derivation" $
        derivation p g0
          @?= [[AndNode (Occ (head g0) [0] (IntSet.delete 0 all4) mempty)
                        (IntMap.singleton 0 Void)]]
    , testCase "A derivation of possible substitutions for a variable" $
        derivation p gx
          @?=
          [
            [AndNode (Occ (head gx) [0] all4 $ IntSet.singleton v100) mempty]
          , (\(i,a) -> AndNode (Occ a [0] (IntSet.delete i all4) mempty)
                               (IntMap.singleton i Void)) <$>
            zip [0..] (map clHead $ take 2 p)
          ]
    ]-}
  where
    vv0 = Var v0
    c0 = Fun "0" []
    bit x = Fun "bit" [x]
--    cempty = Con "empty"
    s0 = singleton v0 c0
--    all4 = IntSet.fromList [0..3]
--    len = length p
