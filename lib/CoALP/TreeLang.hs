-- |
-- * Tree languages.

module CoALP.TreeLang
       (
         -- | Types.
         TreeLang,
         TreeWord,
         N,
         -- | Operations on languages (extendible list).
         empty,
         singleton,
         (\:),
         -- | Correctness check.
         isTreeLang,
         -- | Functions on underlying types.
         isPrefix
       ) where

import Prelude hiding (foldr, zip, length, all, drop)

import Data.Sequence (Seq, ViewR(..), (|>), viewr, length, zip, drop)
import qualified Data.Sequence as Seq
import Data.Set (Set, member)
import qualified Data.Set as Set
import Data.Foldable
import Data.Word

type TreeLang = Set TreeWord  -- ^ A tree language is a set of words.
type TreeWord = Seq N         -- ^ A word is a list of symbols.
type N        = Word64        -- ^ A symbol is an unsigned integer.

empty :: TreeLang
empty = Set.empty

singleton :: TreeLang
singleton = Set.singleton Seq.empty

-- ^ Tree sub-language (left quotient) at a given word.
(\:) :: TreeWord -> TreeLang -> TreeLang
(\:) u = foldr quotients empty
  where
    quotients v =
      if u `isPrefix` v then Set.insert $ drop (length u) v else id

-- | Run-time check of a set against the definition of term tree. The finite
-- branching property is not checked because the number of children of a tree
-- node is at most 2^64 for 'Word64'.
isTreeLang :: TreeLang -> Bool
isTreeLang l = all check l
  where
    check w = case viewr w of
      EmptyR -> True
      v :> 0 -> v            `member` l
      v :> i -> (v |> i - 1) `member` l

isPrefix :: TreeWord -> TreeWord -> Bool
isPrefix u v =
  let pairs = u `zip` v in
  length pairs == length u && all (uncurry (==)) pairs
