-- |
-- * Tree languages.

module CoALP.TreeLang where

import Prelude hiding (foldr)

import Data.Sequence
import Data.Set
import Data.Word

type TreeLang = Set TreeWord  -- ^ A tree language is a set of words.
type TreeWord = Seq TreeSymb  -- ^ A word is a list of symbols.
type TreeSymb = Word64        -- ^ A symbol is an unsigned integer.

-- | Run-time check of a set against the definition of term tree. The finite
-- branching property is not checked because the number of children of a tree
-- node is at most 2^64 for 'Word64'.
treeLang :: TreeLang -> Bool
treeLang l = foldr check True l
  where
    check w b = case viewr w of
      EmptyR -> b
      v :> 0 -> v `member` l
      v :> i -> (v |> i - 1) `member` l
