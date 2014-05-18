-- |
-- * Mode annotations

module CoALP.Mode where

import CoALP.Term

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable

-- | Type of argument mode. A mode of an argument to a predicate consists of
--
-- - data flow direction: either input (+) or output (-);
--
-- - evaluation order:    either eager (!) or lazy   (?).
--
-- Data flow directions are related to the quality of the argument to have
-- variables. If the argument term is ground then it has input direction by
-- default, unless the _tree evaluation context_ implies that is has output
-- direction. Note however that even if the context suggests the output
-- direction for a ground term, this is equivalent to evaluating that term in
-- the input direction since no evaluation of that term is possible at all. Data
-- flow directions help define an evaluation context which is a broader notion
-- to simply argument modes (such as "ground" and "any").
--
-- One argument is allowed to have different modes. There is a semantic
-- subsumption relation on modes which affects interpretation of mode
-- annotations:
--
-- 1. Output eagerly (-!) implies output lazily (-?).
--
-- 2. Input lazily (+?) implies input eagerly (+!). (Dually to 1.)
--
-- In short, -! => -? and +? => +! .
--
-- For example, for a binary predicate @p@, the annotation @p -! +?@ implies @p
-- -? +!@. Therefore, if both annotations are given for the same program, the
-- effect will be the same as if only the most concrete, @p -! +?@, were given.
--
data Mode = M Direction Order
  deriving Eq

instance Hashable Mode where
  hashWithSalt s (M d o) = s `hashWithSalt` d `hashWithSalt` o

instance Ord Mode where
  (<=) (M Input  ordl) (M Input  ordr) = ordl >= ordr
  (<=) (M Output ordl) (M Output ordr) = ordl <= ordr
  (<=) _ _ = False  -- FIXME: incomparable modes, (<=) is not boolean here, and
                    -- the definition of (_>_) as (not (_<=_)) should be
                    -- prohibited. A proper partial ordering should be used
                    -- instead of Ord.

-- | Data flow direction.
data Direction = Input  -- ^ ground: no variables.
               | Output -- ^ any: there may or may not be variables.
  deriving (Eq, Ord)

instance Hashable Direction where
  hashWithSalt s Input  = s `hashWithSalt` (0x620d :: Int)
  hashWithSalt s Output = s `hashWithSalt` (0xa44 :: Int)

-- | Order of evaluation.
data Order = Eager  -- ^ No restriction on computation of mgu for this argument.
           | Lazy   -- ^ Compute mgus for variables in this argument at most
                    -- once, unless no solution is found, in which case another
                    -- lazy computation of mgus is allowed.
  deriving (Eq, Ord)

instance Show Order where
  show Eager  = "!"
  show Lazy   = "?"

instance Hashable Order where
  hashWithSalt s Eager = s `hashWithSalt` (0x3A637 :: Int)
  hashWithSalt s Lazy  = s `hashWithSalt` (0x07A27 :: Int)

-- | Association of a predicate name (constructor identifier) to a set of
-- annotations of its arguments with modes.
newtype ModeAssoc = ModeAssoc (HashMap Ident (HashSet [Mode])) deriving Eq

unionModeAssoc :: [ModeAssoc] -> ModeAssoc
unionModeAssoc massocs =
  ModeAssoc $ foldr (HashMap.unionWith HashSet.union) HashMap.empty assocs
  where
    assocs = map (\(ModeAssoc ma) -> ma) massocs
