{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ConstraintKinds, KindSignatures, TypeFamilies, StandaloneDeriving #-}

-- |
-- * Substitution and unification.

module CoALP.Subst where

import Prelude hiding ( foldr, any )
import GHC.Exts

import CoALP.Term

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
--data Subst m a b where
--  Subst :: (Hashable a, Hashable b) => HashMap a (m b) -> Subst m a b

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
{-
  hash s =
    HashMap.foldrWithKey (\v t h -> h `xor` (hash v `rotate` 2)
                                      `xor` (hash t `rotate` (-3))
                         ) 0x5B57 s
-}

-- | The structure of the Kleisli category for a monad with constraints.
class KleisliC (cat :: (* -> *) -> * -> * -> *)  where
  type KleisliC1 a :: Constraint
  type KleisliC1 a = ()

  type KleisliC2 m a b c :: Constraint
  type KleisliC2 m a b c = ()

  idc   :: KleisliC1 a       => cat m a a
  compc :: KleisliC2 m a b c => cat m b c -> cat m a b -> cat m a c

instance KleisliC Subst where
  type KleisliC1 a = (Eq a, Hashable a)
  type KleisliC2 m a b c =
    (Monad m, Eq a, Hashable a, Eq b, Hashable b, Hashable c,
     Injectable b c, Injectable b a)
  idc   = identity
  compc = flip compose

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

-- | Substitution error reporting in a monad context.
substError :: Monad m => SubstError -> m SubstOut
substError = return . Left

-- | Immediately returns a substitution in a monad context.
substFound :: (Monad m, MonadState s m) => s -> m SubstOut
substFound s = put s >> return (Right ())

-- | Returns a substitution in a 'Term' monad context. Performs occurs check.
checkSubstFound :: (Eq a, Eq b, Hashable b) => Subst (Term a) b b ->
                   SubstComput (Term a) b b
checkSubstFound s@(Subst sm) =
  put s >>
  return (
    if HashMap.null $ HashMap.filterWithKey loopy sm
    then Right ()
    else Left OccursCheckFailed
         )
  where
    loopy v t = isFun t && any (== v) t

checkSubstFoundPos :: (Eq a, Eq b, Hashable b, Eq c, Enum c, Hashable c) =>
                      State ([c], HashSet [c], Subst (Term a) b b)
                            (Either SubstError (HashSet [c]))
checkSubstFoundPos = do
  (pos, acc, Subst s) <- get
  return (
    if HashMap.null $ HashMap.filterWithKey loopy s
    then (Right $ HashSet.insert pos acc)
    else (Left OccursCheckFailed)
         )
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

-- | Computes an mgu in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
mguTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
           Term a b -> Term a b -> SubstComput (Term a) b b
mguTerm (Var v) t   = checkSubstFound $ singleton v t
mguTerm t u@(Var _) = mguTerm u t
mguTerm (Fun c ts) (Fun d us)
  | c == d    = chainMgu mguTerm ts us
  | otherwise = substError IdentMismatch

-- | Computes a match in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
matchTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
             Term a b -> Term a b -> SubstComput (Term a) b b
matchTerm (Var v) t = substFound $ singleton v t
matchTerm (Fun c ts) (Fun d us)
  | c == d    = chainMatch matchTerm ts us
  | otherwise = substError IdentMismatch
matchTerm _ _ = substError NonMatchable

-- | Computes a variable renaming in the state monad.
--
-- FIXME: disregards the starting state when binding variables to terms.
renameTerm :: (Eq a, Eq b, Hashable b, Injectable b b) =>
              Term a b -> Term a b -> SubstComput (Term a) b b
renameTerm (Var v) t@(Var _) = substFound $ singleton v t
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
chainMgu _ []       []       = substFound $ identity
chainMgu f (t : ts) (u : us) = do
  rl <- f t u
  case rl of
    Right _ -> do
      sl <- get
      let appl = (>>= subst sl)  -- if HashMap.null sl then id else (>>= subst sl)
      rr <- chainMgu f (appl <$> ts) (appl <$> us)
      case rr of
        Right _ -> checkSubstFound . compose sl =<< get
        e -> return e
    e -> return e
chainMgu _ _ _ = substError ArgumentsDontAlign

-- | Chains a computation of match-type substitution (not rewriting the terms)
-- through a pair of lists of terms where return from a recursive call merges
-- the substitution.
chainMatch :: (Eq a, Eq b, Hashable b, Injectable b b) =>
              (Term a b -> Term a b -> SubstComput (Term a) b b) ->
              [Term a b] -> [Term a b] -> SubstComput (Term a) b b
chainMatch _ []           []       = substFound identity
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
    substFound $ Subst $ msl `HashMap.union` msr
  where
    vs = HashSet.toList $ HashSet.unions $ varsTerm <$> ts
    disagree (t0, t1, t2) = t0 /= t1 && t0 /= t2 && t1 /= t2
