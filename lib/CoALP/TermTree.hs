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
import Data.Sequence ((|>))
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
    respectArity w = case t!w of
      Right _ -> not $ (w |> 0) `member` l
      Left a  -> a `member` symbols sg &&
                 let ar = arity sg ! a in
                 -- sufficient condition
                 if (ar > 0) then (w |> ar - 1) `member` l else True &&
                 -- necessary condition
                 not ((w |> ar) `member` l)
