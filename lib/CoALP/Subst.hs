{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ConstraintKinds, KindSignatures, TypeFamilies, StandaloneDeriving #-}

-- |
-- * Substitution and unification.

module CoALP.Subst where

import Prelude hiding ( foldr, any, all )

import CoALP.Term

import Control.Arrow
import Control.Monad.State.Lazy
import Control.Applicative
import Control.DeepSeq
import qualified Data.HashSet as HashSet
import Data.HashSet (HashSet)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy (HashMap)
import Data.Hashable
import Data.Foldable
--import Data.Bits

-- | The optimised type of substitution. It differs from the usual type of
-- 'Kleisli' arrow of a monad @m@ in that it has a 'HashMap' implementation
-- rather than a purely functional implementation.
newtype Subst m a b = Subst {unSubst :: HashMap a (m b)}

deriving instance (Eq a, Eq (m b)) => Eq (Subst m a b)

-- | First-order substitution (of first-order terms for integer-numbered
-- variables).
type Subst1 = Subst (Term String) Int Int

instance (NFData a, NFData (m b), Hashable a, Hashable b) =>
         NFData (Subst m a b) where
  rnf (Subst s) = s `deepseq` ()

-- | An instance for hashing substitutions.
instance (Hashable a, Hashable (m b)) => Hashable (Subst m a b) where
  hashWithSalt salt (Subst s) =
    hashWithSalt salt $
    HashMap.foldrWithKey (\v t h -> h `hashWithSalt` v `hashWithSalt` t) 0x5B57 s

-- | The canonical representation of the identity substitution.
identity :: (Eq a, Hashable a) => Subst m a a
identity = Subst $ HashMap.empty

-- | The singleton substitution.
singleton :: (Eq a, Hashable a, Hashable b) => a -> m b -> Subst m a b
singleton i t = Subst $ HashMap.singleton i t

class Injectable a b where
  inject :: a -> b

instance Injectable Int Int where
  inject = id

instance (Monad m, Injectable a b) => Injectable (m a) (m b) where
  inject = (>>= return . inject)

instance (Monad m, Hashable a, Eq b, Hashable b, Injectable a b) =>
         Injectable (Subst m a c)
                    (Subst m b c) where
  inject (Subst s) =
    Subst $ foldr (\(a, c) -> HashMap.insert (inject a) c)
                  HashMap.empty $
                  HashMap.toList s

-- | Convertor of substitutions from the hash map representation to the
-- functional representation. Useful with monadic bind, etc.
subst :: (Monad m, Eq a, Hashable a, Hashable b, Injectable a b) =>
         Subst m a b -> a -> m b
subst (Subst s) a =
  case HashMap.lookup a s of
    Just t  -> t
    Nothing -> return $ inject a

-- | Composition of substitutions.
--
-- FIXME: 1) Serialisation of 'HashMap' into a list is made. This is only needed
-- when @a@ and @b@ are different types. For the reasons of run-time efficiency,
-- and to drop the mechanic constraint @Injectable b b@ in a number of
-- functions, consider adding a specialised composition of substitutions for the
-- case where @a@ and @b@ are the same type.
--
-- 2) The instance of 'Injectable' on 'Subst' is useless so far and code is
-- copied to solve the overlapping instances problem.
compose :: (Monad m, Eq a, Hashable a, Eq b, Hashable b, Hashable c,
            Injectable b c, Injectable b a) =>
           Subst m a b -> Subst m b c -> Subst m a c
compose (Subst sab) sb@(Subst sbc) =
  Subst $ HashMap.foldrWithKey (\a -> HashMap.insert a . (>>= subst sb)) sac sab
  where
--    Subst sac = inject sb
    sac = foldr (\(a, c) -> HashMap.insert (inject a) c)
                HashMap.empty $
                HashMap.toList sbc

-- | Errors in computation of a substitution.
data SubstError = IdentMismatch
                | NonMatchable
                | NonRenameable
                | ArgumentsDontAlign
                | DisagreementOnVariables
                | OccursCheckFailed
                deriving (Show, Eq)

-- | Computation of a substitution
type SubstOut = Either SubstError ()
type SubstComput m a b = State (Subst m a b) SubstOut

-- | Type of subterm position. Positions are little-endian: from leaves to the
-- root, because this way they are appended by consing, if recursing from the
-- root. And because they are not currently used for traversal but only for
-- comparson by equality, the endianness is inessential.
type Pos = [Int]

-- | Sets of positions. These are required for the mgu guardedness check.
type PosSet = HashSet Pos

-- | Substitution error reporting in a monad context.
substError :: Monad m => SubstError -> m SubstOut
substError = return . Left

-- | Immediately returns a substitution in a monad context.
substFound :: Monad m => m SubstOut
substFound = return $ Right ()

-- | Returns a substitution in a 'Term' monad context. Performs occurs check.
checkSubstFound :: (Eq a, Eq b, Hashable b) => SubstComput (Term a) b b
checkSubstFound = do
  Subst s <- get
  return (
    if HashMap.null $ HashMap.filterWithKey loopy s
    then Right ()
    else Left OccursCheckFailed
         )
  where
    loopy v t = isFun t && any (== v) t

checkSubstFoundPos :: (Eq a, Eq b, Hashable b) => Pos ->
                      State (PosSet, Subst (Term a) b b) SubstOut
checkSubstFoundPos p = do
  (ps, Subst s) <- get
  if HashMap.null $ HashMap.filterWithKey loopy s
    then do
        put (HashSet.insert p ps, Subst s)
        return $ Right ()
    else
        return $ Left OccursCheckFailed
  where
    loopy v t = isFun t && any (== v) t

-- | Most general unifier.
--
-- Error messages are not returned but all mapped to 'Nothing'. This is only for
-- compatibility with the previous, simplistic interface to computations of
-- substitutions. If error message handling or starting from a non-identity
-- substitution is needed, see 'mguTerm' instead.
mguMaybe :: (Eq a, Eq b, Hashable b, Injectable b b) =>
            Term a b -> Term a b -> Maybe (Subst (Term a) b b)
mguMaybe t u = runSubstComputMaybe mguTerm t u

-- | Term matching, a.k.a. subsumption.
matchMaybe :: (Eq a, Eq b, Hashable b, Injectable b b) =>
              Term a b -> Term a b -> Maybe (Subst (Term a) b b)
matchMaybe t u = runSubstComputMaybe matchTerm t u

-- | Computes a variable renaming iff the given terms are equivalent up to
-- variable renaming; otherwise returns an error value.
renameMaybe :: (Eq a, Eq b, Hashable b, Injectable b b) =>
               Term a b -> Term a b -> Maybe (Subst (Term a) b b)
renameMaybe t u = runSubstComputMaybe renameTerm t u

-- | A helper function to run substitution computations starting from the
-- identity substitution.
runSubstComput :: (Eq b, Hashable b) =>
                  (m b -> m b -> SubstComput (Term a) b b) ->
                  m b -> m b -> (SubstOut, Subst (Term a) b b)
runSubstComput f a1 a2 = runState (f a1 a2) identity

-- | A helper function for compatibility with the old interface that returned
-- 'Maybe' substitutions.
runSubstComputMaybe :: (Eq b, Hashable b) =>
                       (m b -> m b -> SubstComput (Term a) b b) ->
                       m b -> m b -> Maybe (Subst (Term a) b b)
runSubstComputMaybe f a1 a2 =
  case runState (f a1 a2) identity of
    (Right _, s) -> Just s
    _            -> Nothing

-- | Runs a position-recording substitution computation.
runSubstComputPos :: (Eq b, Hashable b) =>
                  (m b -> (Pos, m b) ->
                   State (PosSet, Subst (Term a) b b) SubstOut) ->
                  m b -> m b -> (SubstOut, (PosSet, Subst (Term a) b b))
runSubstComputPos f a1 a2 = runState (f a1 ([], a2)) (HashSet.empty, identity)

-- | Same as 'runSubstComputPos' but forgets the error messages.
runSubstComputPosMaybe :: (Eq b, Hashable b) =>
                          (m b -> (Pos, m b) ->
                           State (PosSet, Subst (Term a) b b) SubstOut) ->
                          m b -> m b -> Maybe (PosSet, Subst (Term a) b b)
runSubstComputPosMaybe f a1 a2 =
  case runState (f a1 ([], a2)) (HashSet.empty, identity) of
    (Right _, s) -> Just s
    _            -> Nothing

-- | Computes an mgu in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
mguTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
           Term a b -> Term a b -> SubstComput (Term a) b b
mguTerm (Var v) t   = put (singleton v t) >> checkSubstFound
mguTerm t u@(Var _) = mguTerm u t
mguTerm (Fun c ts) (Fun d us)
  | c == d    = chainMgu mguTerm ts us
  | otherwise = substError IdentMismatch

-- | The mgu computation that records the positions of the matching subterms
-- only of the right term.
--
-- FIXME: Consider the incoming substitution rather than discarding it.
mguTermPos :: (Eq a, Eq b, Hashable b, Injectable b b) =>
           (Term a b) -> (Pos, Term a b) ->
           State (PosSet, Subst (Term a) b b) SubstOut
mguTermPos (Var v) (p, t) = do
  (ps, _) <- get
  put (ps, singleton v t)
  checkSubstFoundPos p
mguTermPos t (p, Var v) = do
  (ps, _) <- get
  put (ps, singleton v t)
  checkSubstFoundPos p
mguTermPos (Fun c ts) (p, Fun d us)
  | c == d = chainMguPos mguTermPos ts $
             ((:p) *** id) <$> zip [0..length us - 1] us
  | otherwise = substError IdentMismatch

-- | Computes a match in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
matchTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
             Term a b -> Term a b -> SubstComput (Term a) b b
matchTerm (Var v) t = put (singleton v t) >> substFound
matchTerm (Fun c ts) (Fun d us)
  | c == d    = chainMatch matchTerm ts us
  | otherwise = substError IdentMismatch
matchTerm _ _ = substError NonMatchable

-- | Computes a variable renaming in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
renameTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
              Term a b -> Term a b -> SubstComput (Term a) b b
renameTerm (Var v) t@(Var _) = put (singleton v t) >> substFound
renameTerm (Fun c ts) (Fun d us)
  | c == d     = chainMatch renameTerm ts us
  | otherwise  = substError IdentMismatch
renameTerm _ _ = substError NonRenameable

-- | Chains a computation of mgu-type substitution (rewriting both in the first
-- and second terms) through a pair of lists of terms where return from a
-- recursive call accumulates the substitution by composition.
chainMgu :: (Eq a, Eq b, Hashable b, Injectable b b) =>
            (Term a b -> Term a b -> SubstComput (Term a) b b) ->
            [Term a b] -> [Term a b] -> SubstComput (Term a) b b
chainMgu _ []       []       = put identity >> substFound
chainMgu f (t : ts) (u : us) = do
  rl <- f t u
  case rl of
    Right _ -> do
      sl <- get
      let appl = (>>= subst sl)  -- if HashMap.null sl then id else (>>= subst sl)
      rr <- chainMgu f (appl <$> ts) (appl <$> us)
      case rr of
        Right _ -> do
                   sr <- get
                   put (compose sl sr)
                   checkSubstFound
        e -> return e
    e -> return e
chainMgu _ _ _ = substError ArgumentsDontAlign

chainMguPos :: (Eq a, Eq b, Hashable b, Injectable b b) =>
               (Term a b -> (Pos, Term a b) ->
                State (PosSet, Subst (Term a) b b) SubstOut) ->
               [Term a b] -> [(Pos, Term a b)] ->
               State (PosSet, Subst (Term a) b b) SubstOut
chainMguPos _ [] [] = do
  (ps, _) <- get
  put (ps, identity)
  substFound
chainMguPos f (t : ts) ((p, u) : us) = do
  rl <- f t (p, u)
  case rl of
    Right _ -> do
      (_, sl) <- get
      let appl =        (>>= subst sl)
          appr = id *** (>>= subst sl)
      rr <- chainMguPos f (appl <$> ts) (appr <$> us)
      case rr of
        Right _ -> do
          (pr, sr) <- get
          put (pr, compose sl sr)
          checkSubstFoundPos p
        e -> return e
    e -> return e
chainMguPos _ _ _ = substError ArgumentsDontAlign

-- | Chains a computation of match-type substitution (not rewriting the terms)
-- through a pair of lists of terms where return from a recursive call merges
-- the substitution.
chainMatch :: (Eq a, Eq b, Hashable b, Injectable b b) =>
              (Term a b -> Term a b -> SubstComput (Term a) b b) ->
              [Term a b] -> [Term a b] -> SubstComput (Term a) b b
chainMatch _ []           []       = put identity >> substFound
chainMatch f ts0@(t : ts) (u : us) = do
  rl <- f t u
  case rl of
    Right _ -> do
      sl <- get
      rr <- chainMatch f ts us
      case rr of
        Right _ -> get >>= merge ts0 sl
        e -> return e
    e -> return e
chainMatch _ _ _ = substError ArgumentsDontAlign

-- | A (contextual) merge is the union of two substitutions with the condition
-- that there is no variable, in a given list of terms, that is mapped
-- non-trivially and to different terms by each of the two substitutions. If the
-- condition fails, the merge fails.
merge :: (Eq a, Eq b, Hashable b, Injectable b b) =>
         [Term a b] -> Subst (Term a) b b ->
         Subst (Term a) b b -> SubstComput (Term a) b b
merge ts sl@(Subst msl) sr@(Subst msr) = do
  if any disagree $ zip3 (return <$> vs) (subst sl <$> vs) (subst sr <$> vs) then
    substError DisagreementOnVariables
  else
    put (Subst $ msl `HashMap.union` msr) >> substFound
  where
    vs = HashSet.toList $ HashSet.unions $ varsTerm <$> ts
    disagree (t0, t1, t2) = t0 /= t1 && t0 /= t2 && t1 /= t2

idempotent :: Subst (Term String) Int Int -> Bool
idempotent s = all ((uncurry (==)) . (appl &&& (appl . appl)) . Var) dom
  where
    dom = HashMap.keys $ unSubst s
    appl = (>>= subst s)

idemRenaming :: Subst (Term String) Int Int -> Bool
idemRenaming s = all isVar im && idempotent s
  where
    im = HashMap.elems $ unSubst s
    isVar (Var _) = True
    isVar _       = False
