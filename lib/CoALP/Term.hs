{-# LANGUAGE DeriveGeneric #-}
-- |
-- * Terms

module CoALP.Term where

import Prelude hiding (foldr, foldl, any, concatMap)

import Control.DeepSeq
import Data.Hashable
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Control.Monad
import Control.Applicative
import GHC.Generics (Generic)

-- | Type of term for any type of functional symbol and any type of variable.
data Term a b = Var b              -- ^ a variable
              | Fun a [Term a b]   -- ^ a function
              deriving (Eq, Ord, Generic)

instance (Hashable a, Hashable b) => Hashable (Term a b)

-- | Type of first-order term.
--
-- Identifiers start with a lower-case Latin letter, a decimal digit or a symbol
-- drawn from a limited set not containing the colon which is reserved to the
-- \"from\" separator @:-@ written exactly like in conventional LP. The rest of
-- the identifier may also contain uppercase Latin letters. Examples of
-- identifiers are
--
-- > tYPE     p     <=     0th
--
-- Variables are essentially non-negative integers. However, the user interface
-- allows denoting variables with names that start with an upper-case Latin
-- letter followed by any Latin letters, symbols (same as in identifiers) or
-- decimal digits. The parser then converts variable names to variable
-- numbers. When arbitrary terms are printed, each variable is denoted by a name
-- starting from @X_@ followed by the number of that variable.
--
type Term1 = Term String Int

{-
instance (Hashable a, Hashable b) => Hashable (Term a b) where
  hashWithSalt salt (Var v)    = salt `hashWithSalt` v
  hashWithSalt salt (Fun f ts) = salt `hashWithSalt` f `hashWithSalt` ts
-}

instance (NFData a, NFData b) => NFData (Term a b) where
  rnf (Var b)    = b `deepseq` ()
  rnf (Fun a ts) = a `deepseq` ts `deepseq` ()

type Variable = Int
type Ident = String

instance Monad (Term a) where
  return i       = Var i
  Var i    >>= k = k i
  Fun c ts >>= k = Fun c $ (>>= k) <$> ts

instance Functor (Term a) where
  fmap f (Var i)    = Var   $ f i
  fmap f (Fun c ts) = Fun c $ map (fmap f) ts

instance Foldable (Term a) where
  foldr f z (Var i)    = f i z
  foldr f z (Fun _ ts) = foldr (flip (foldr f)) z ts

  foldl f z (Var i)    = f z i
  foldl f z (Fun _ ts) = foldl (foldl f) z ts

instance Traversable (Term a) where
  traverse f (Var i)    = Var   <$> f i
  traverse f (Fun c ts) = Fun c <$> traverse (traverse f) ts

instance Applicative (Term a) where
  pure  = return
  (<*>) = ap

maxVarTerm :: Term1 -> Maybe Int
maxVarTerm = foldr (max . Just) Nothing

isGround :: Term1 -> Bool
isGround = isNothing . maxVarTerm

type VarSet = IntSet

varsTerm1 :: Term1 -> VarSet
varsTerm1 (Var v)    = IntSet.singleton v
varsTerm1 (Fun _ ts) = IntSet.unions $ varsTerm1 <$> ts

varsTerm :: (Eq b, Hashable b) => Term a b -> HashSet b
varsTerm (Var v)    = HashSet.singleton v
varsTerm (Fun _ ts) = foldr (HashSet.union . varsTerm) HashSet.empty ts

mapf :: (a -> c) -> Term a b -> Term c b
mapf _ (Var b)    = Var b
mapf f (Fun a ts) = Fun (f a) $ mapf f <$> ts

foldrf :: (Either a b -> c -> c) -> c -> Term a b -> c
foldrf f z (Var b)    = f (Right b) z
foldrf f z (Fun a ts) = foldr (flip (foldrf f)) (f (Left a) z) ts

isFun :: Term a b -> Bool
isFun (Fun _ _) = True
isFun _         = False

type PositionalTerm a b c = Term (a, [c]) (b, [c])

-- | Labels subterms of a given term with words of a tree language.
labelSubterms :: Enum c => Term a b -> PositionalTerm a b c
labelSubterms = go [] where
  go cs (Var b)    = Var (b, cs)
  go cs (Fun f ts) = Fun (f, cs) $
                     (\(t, c) -> go (cs ++ [c]) t) <$>
                     zip ts (enumFrom (toEnum 0))

-- | Term reduct:
--
-- > t `reduct` s
--
-- is @True@ if and only if @t@ is a reduct of @s@.
reduct :: Eq a => Term a b -> Term a b -> Bool
reduct (Var _)    (Fun _ (_:_)) = True
reduct (Fun _ []) (Fun _ (_:_)) = True
reduct (Fun f ts) (Fun g us) | f == g = any (uncurry reduct) (zip ts us)
reduct _ _ = False

-- | Recursive variable or constant reduction measures with positions in the
-- first term.
recReducts :: (Eq a, Eq b) => Term a b -> Term a b -> [([Int], Term a b)]
recReducts = go []
  where
    go w (Var i)    u@(Fun _ (_:_)) = if any (== i) u then [(w, u)] else []
    go w (Fun c []) u@(Fun _ (_:_)) = foldrf ((++) . samecon) [] u
      where
        samecon (Left d) | d == c = [(w, u)]
        samecon _                 = []
    go w (Fun f ts) (Fun g us)
      | f == g =
        (\(t, u, i) -> go (w ++ [i]) t u) `concatMap` zip3 ts us [0..]
    go _ _ _ = []

-- | Variable reduction measures with positions in the first term.
varReducts :: (Eq a, Eq b) => Term a b -> Term a b -> [([Int], Term a b)]
varReducts = go []
  where
    go w (Var _) u@(Fun _ (_:_)) = [(w, u)]
    go w (Fun f ts) (Fun g us)
      | f == g =
        (\(t, u, i) -> go (w ++ [i]) t u) `concatMap` zip3 ts us [0..]
    go _ _ _ = []

-- | Recursive variable reduction measures with positions in the first term.
recVarReducts :: (Eq a, Eq b) => Term a b -> Term a b -> [([Int], Term a b)]
recVarReducts = go []
  where
    go w (Var i) u@(Fun _ (_:_)) = if any (== i) u then [(w, u)] else []
    go w (Fun f ts) (Fun g us)
      | f == g =
        (\(t, u, i) -> go (w ++ [i]) t u) `concatMap` zip3 ts us [0..]
    go _ _ _ = []

nonVarSubterms :: Term a b -> [([Int], Term a b)]
nonVarSubterms (Var _)      = []
nonVarSubterms t0@(Fun _ _) = tail $ go [] t0
  where
    go _ (Var _) = []
    go w t@(Fun _ us) = (w, t) :
                        (\(i, u) -> go (w ++ [i]) u) `concatMap` (zip [0..] us)
