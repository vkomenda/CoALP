-- |
-- * Guardedness checks

module CoALP.Guards
       (
         guarded
       , guardedClauses
       , guardedMatches
       , guardedMgus
       )
       where

import CoALP.Term
import CoALP.Clause
import CoALP.Subst

import Control.Arrow
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Hashable
import Data.Maybe
import Data.Function
import Control.Applicative

type Arity     a   = (a, Int)
type Vars        b = HashSet b
type ArityVars a b = (Arity a, Vars b)
type Count         = Int
type CountVars   b = (Count, Vars b)

-- | For each occurrence of a functional symbol, stores its arity and variables
-- under that occurrence.
arityVarsTerm :: (Eq b, Hashable b) => Term a b -> Term (ArityVars a b) b
arityVarsTerm (Var b)    = Var b
arityVarsTerm (Fun a ts) = Fun ((a, length ts), HashSet.unions $ vars <$> avs) avs
  where
    avs = map arityVarsTerm ts
    vars (Var b)         = HashSet.singleton b
    vars (Fun (_, vs) _) = vs

-- | Counts all occurrences of each aritied functional symbol, and all variables
-- under any of those occurrences. Modified: It takes now an extra argument that is
-- a HashMap that will be the initial value.
countVars :: (Eq a, Eq b, Hashable a, Hashable b) =>
             Term (ArityVars a b) b -> HashMap (Arity a) (CountVars b) ->
             HashMap (Arity a) (CountVars b)
countVars t h = foldrf get h t
  where
    get (Left (ar, vs)) m = HashMap.insertWith add ar (1, vs) m
    get _               m = m
    add (c, v) (c0, v0)   = (c0 + c, HashSet.union v0 v)

-- | Static guardedness check by finding immediately decreasing structure.
guardedClause :: (Eq a, Eq b, Hashable a, Hashable b) => Clause a b -> Bool
guardedClause (Fun c ts :- b) = all guardedAtom b
  where
    arity = length ts
    av = countVars . arityVarsTerm
    av0 = flip av HashMap.empty

--  commonFuncsDecrease :: (Term a b, Term a b) -> HashMap (Arity a) Bool
    commonFuncsDecrease (t, u) = HashMap.intersectionWith
      (\(ct, vst) (cu, vsu) ->
        ct > cu && HashSet.null (HashSet.difference vsu vst)
      )
      avt $
--      allVars0 <$>
      (av u $ const (0, HashSet.empty) <$> avt)
      where
        avt = av0 t
{-
        allVars0 ov@(occ, _)
          | occ == 0  = (occ, varsTerm u)
          | otherwise = ov
-}
    guardedAtom (Fun d us)
      | c /= d || arity /= length us = True
      | otherwise = any (== True) $
                    any (== True) . HashMap.elems . commonFuncsDecrease <$>
                    zip ts us
    guardedAtom (Var _) = False
guardedClause (Var _ :- _) = False

-- | Guardedness check 1. Loop detection within clauses.
guardedClauses :: (Eq a, Eq b, Hashable a, Hashable b) => Program a b -> Bool
guardedClauses (Pr cls) = all guardedClause cls

--                       predicate->clause  -> set of args
type BranchHistory a b = HashMap a (IntMap (HashSet [Term a b]))

-- | The loop detection functional, to compute a fixed point that takes the
-- following arguments:
--
--  # a history of matches for each predicate symbol above the root,
--  # the program,
--  # the root term.
guardedFun :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b,
               Injectable b b) =>
              (BranchHistory a b -> Program a b -> Term a b -> Bool) ->
              BranchHistory a b -> Program a b -> Term a b -> Bool
guardedFun f hist pr@(Pr cls) h@(Fun c ts) =
  all (\(i, s) ->
        (all (recReduct h . Fun c) . HashSet.toList <$> mvis i)
          /= Just False &&
        all (f (hist_h i) (liftPr (hist_h i) pr) . (>>= subst s)) (clBody (cls!!i))
      ) $ h `matchHeads` cls
  where
    mvis i   = return =<< IntMap.lookup i =<< HashMap.lookup c hist
    hist_h i = HashMap.insertWith
                 (IntMap.unionWith HashSet.union)
                 c
                 (IntMap.singleton i $ HashSet.singleton ts)
                 hist
guardedFun _ _ _ (Var _) = False

-- | Variable renaming in the given program: increment by 1 plus the maximum
-- variable number in the given branch history.
liftPr :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b) =>
          BranchHistory a b -> Program a b -> Program a b
liftPr hist pr = Pr $ liftVarsClause ((+1) <$> maxVarHistory hist) <$> unPr pr

-- | Loop detection under matches.
guardedMatch :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b,
                 Injectable b b) =>
                BranchHistory a b -> Program a b -> Term a b -> Bool
guardedMatch = fix guardedFun

-- | Guardedness check 2. Loop detection under matching.
guardedMatches :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b,
                   Injectable b b) =>
                  Program a b -> Bool
guardedMatches pr@(Pr cls) = all (guardedMatch HashMap.empty pr . clHead) cls

-- | Map a match against a given term over the heads of a given list of clauses.
matchHeads :: (Eq a, Eq b, Hashable a, Hashable b, Injectable b b) =>
              Term a b -> [Clause a b] -> [(Int, Subst (Term a) b b)]
matchHeads = onHeads matchMaybe

-- | Map a mgu computation against a given term over the heads of a given list
-- of clauses.
mguHeads :: (Eq a, Eq b, Hashable a, Hashable b, Injectable b b) =>
            Term a b -> [Clause a b] -> [(Int, Subst (Term a) b b)]
mguHeads = onHeads mguMaybe

-- | Map a computation on a given term over the heads of a given list of
-- clauses.
onHeads :: (Eq a, Eq b, Hashable a, Hashable b, Injectable b b) =>
           (Term a b -> Term a b -> Maybe (Subst (Term a) b b)) ->
           Term a b -> [Clause a b] -> [(Int, Subst (Term a) b b)]
onHeads f h =
  mapMaybe (\(i, t) -> f t h >>= \s -> return (i, s)) . zip [0..] . map clHead

-- | 'Just' the maximum variable number in the branch history, if the history
-- contains a variable; otherwise 'Nothing'.
maxVarHistory :: (Hashable b, Ord b, Num b) => BranchHistory a b -> Maybe b
maxVarHistory =
  (HashMap.foldr $ flip $ IntMap.foldr $ flip $ HashSet.foldr $ flip $ foldr $
   \t n -> n `max` foldr (max . Just) Nothing (HashSet.toList $ varsTerm t)
  ) Nothing

-- | A common underlying type of 'clause projection' and 'guarding context'.
data GuardCtx a b = GuardCtx
                    {
                      gcClauseIdx :: Int,
                      gcGuards    :: HashSet (Pos, Term a b)
                    }

type BranchPosHistory a b = HashMap a (IntMap (HashSet Pos, HashSet [Term a b]))

maxVarPosHistory :: (Hashable b, Ord b, Num b) => BranchPosHistory a b -> Maybe b
maxVarPosHistory =
  (HashMap.foldr $ flip $ IntMap.foldr $ flip $ HashSet.foldr $ flip $ foldr $
   \t n -> n `max` foldr (max . Just) Nothing (HashSet.toList $ varsTerm t)
  ) Nothing

liftPrPos :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b) =>
          BranchPosHistory a b -> Program a b -> Program a b
liftPrPos hist pr = Pr $ liftVarsClause ((+1) <$> maxVarPosHistory hist) <$> unPr pr

guardedPosFun :: (Eq a, Eq b, Hashable a, Hashable b, Num b, Ord b,
               Injectable b b) =>
              (BranchPosHistory a b -> Program a b -> Term a b -> Bool) ->
              BranchPosHistory a b -> Program a b -> Term a b -> Bool
guardedPosFun f hist pr@(Pr cls) h@(Fun c ts) =
  all (\(i, s) ->
        (all (guardedClause . flip (:-) [h] . Fun c) . HashSet.toList <$> mvis i)
          /= Just False &&
        all (f (hist_h i) (liftPrPos (hist_h i) pr) . (>>= subst s)) (clBody (cls!!i))
      ) $ h `matchHeads` cls
  where
    mvis i   = snd <$> (IntMap.lookup i =<< HashMap.lookup c hist)
    hist_h i = HashMap.insertWith
                 (IntMap.unionWith (\(ps1, ts1) (ps2, ts2) ->
                                     (HashSet.union ps1 ps2, HashSet.union ts1 ts2)))
                 c
                 (IntMap.singleton i $ (HashSet.empty, HashSet.singleton ts))
                 hist
guardedPosFun _ _ _ (Var _) = False

-- | Loop detection under mgus with a root term and history of unifications for
-- each predicate symbol above the root.
--
-- FIXME: reduce code duplication with 'guardedMatch'.
guardedMgu :: (Eq a, Eq b, Hashable a, Hashable b, Ord b, Num b,
               Injectable b b) =>
              BranchPosHistory a b -> Program a b -> Term a b -> Bool
guardedMgu hist pr@(Pr cls) h@(Fun c _)
  | null matches =
    all (\(i, s) ->
          let hist_s  = fmap (fmap (id *** HashSet.map (map (>>= subst s)))) hist
              h_s     = h >>= subst s in
          null (clBody (cls!!i)) ||
          null (h_s `matchHeads` cls) ||
          maybe (guardedMgu hist_s (liftPrPos hist_s pr) h_s)
                (all (guardedClause . flip (:-) [h_s] . Fun c) . HashSet.toList)
                (mvis i hist_s)
        ) $ h `mguHeads` cls
  | otherwise = guardedPosFun guardedMgu hist pr h
  where
    matches = h `matchHeads` cls
    mvis i hi = return =<< IntMap.lookup i =<< HashMap.lookup c hi
guardedMgu _ _ (Var _) = False

-- | Guardedness check 3. Loop detection under unification.
guardedMgus :: (Eq a, Eq b, Hashable a, Hashable b, Ord b, Num b,
                Injectable b b) =>
               Program a b -> Bool
guardedMgus pr@(Pr cls) = all (guardedMgu HashMap.empty pr . clHead) cls

-- | The main interface to guardedness checks.
guarded :: (Eq a, Eq b, Hashable a, Hashable b, Ord b, Num b,
            Injectable b b) =>
           Program a b -> Bool
guarded pr = guardedClauses pr && guardedMatches pr && guardedMgus pr
