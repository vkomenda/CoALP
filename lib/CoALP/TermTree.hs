{-# LANGUAGE TypeOperators #-}

module CoALP.TermTree
       (
         Symbol,
         Var,
         Sig,
         TermTree(..),
         isTermTree
       ) where

import Prelude hiding (all, length, drop)

import CoALP.TreeLang
import Data.Set (Set, member)
--import qualified Data.Set as Set
import Data.Map (Map, keysSet, (!))
--import qualified Data.Map as Map
import Data.Foldable
import Data.Sequence (ViewL(..), viewl, length, drop, (|>))
       -- FIXME: define operations on underlying types in TreeLang

type Symbol = String
type Var    = N
type (-->)  = Map

data Sig a = Sig {symbols :: Set a, arity :: a --> N}

isSig :: Eq a => Sig a -> Bool
isSig (Sig s ar) = keysSet ar == s

data TermTree a = TermTree {
  sig  :: Sig a,
  lang :: TreeLang,
  tmap :: TreeWord --> Either a Var
  }

isTermTree :: (Eq a, Ord a) => TermTree a -> Bool
isTermTree (TermTree sg l t) =
  isSig sg && isTreeLang l &&
  keysSet t == l && all respectArity l
  where
    noChildren w =  w \: l == singleton
    respectArity w = case t!w of
      Right _ -> noChildren w
      Left a  -> a `member` symbols sg &&
                 let ar = arity sg ! a in
                 -- sufficient condition
                 (w |> ar - 1) `member` l &&
                 -- necessary condition
                 all (\u -> if w `isPrefix` u then
                              case viewl $ drop (length w) u of
                                EmptyL -> True
                                i :< _ -> i < ar
                            else
                              True
                     ) l
