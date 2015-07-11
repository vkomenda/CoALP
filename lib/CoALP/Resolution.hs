{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
module CoALP.Resolution where

import Prelude hiding (all, any, elem, foldr, concat, concatMap, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst
import CoALP.Tree
import CoALP.Derivation

import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.State
import Data.Array ((!), (//))
import Data.Hashable
import qualified Data.Array as Array
import Data.Foldable
import qualified Data.Graph.Inductive as Graph
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List (partition)
import Data.Maybe
import GHC.Generics (Generic)

toBeUnified :: TreeOper1 -> Path -> [Path]
toBeUnified (NodeOper _ b) prefix =
  (\(i, oper) ->
    case oper of
     Left ToBeUnified -> [prefix ++ [i]]
     Right (Just ts)  -> (\(j, t) ->
                           toBeUnified t (prefix ++ [i, j])
                         ) `concatMap` (zip [0..] ts)
     _ -> []
  ) `concatMap` (Array.assocs b)

mguTransitions :: Program1 -> TreeOper1 -> [(Transition, TreeOper1)]
mguTransitions p t = growSuccessful $ failedAndSuccessful $ atBoundary [] t
  where
    growSuccessful :: ([Path], [(Path, Subst1)]) -> [(Transition, TreeOper1)]
    growSuccessful (pts, trs) =
      (\(w, s) ->
        ( Transition w s
        , grow (Just s) w $ (>>= subst s) <$> noMgu pts)
      ) <$> trs

    noMgu :: [Path] -> TreeOper1
    noMgu = foldr (grow Nothing) t

    failedAndSuccessful :: [(a, Maybe b)] -> ([a], [(a, b)])
    failedAndSuccessful =
      (map fst *** map (id *** fromJust)) . partition (isNothing . snd)

    atBoundary :: Path -> TreeOper1 -> [(Path, Maybe Subst1)]
    atBoundary prefix (NodeOper a b) =
      (\(i, oper) ->
        case oper of
         Right (Just ts)  -> (\(j, u) -> atBoundary (prefix ++ [i, j]) u
                             ) `concatMap` (zip [0..] ts)
         Left ToBeUnified -> [( prefix ++ [i]
                              , clHead (liftedClause i) `mguMaybe` a)]
         _ -> []
      ) `concatMap` (Array.assocs b)

    grow :: Maybe Subst1 -> Path -> TreeOper1 -> TreeOper1
    grow ms (i:k:u) (NodeOper a0 b0) =
      NodeOper a0 $ b0 // [(i,
                            case b0!i of
                             Right (Just tbs) ->
                               Right $ Just $
                               take k tbs ++ grow ms u (tbs!!k) :
                               drop (k+1) tbs
                             _ -> error "matchSubtrees: invalid path"
                                  -- TODO: return
                           )]
    grow ms [i] (NodeOper a0 b0) = NodeOper a0 $ b0 // [(i, o)]
      where
        o :: Oper [TreeOper1]
        o | isNothing ms = Right Nothing
          | otherwise    = Right $ Just tbs
        tbs = initTree (Array.bounds $ program p) <$>
              (>>= subst (fromJust ms)) <$> clBody (liftedClause i)
    grow _ _ _ = error "matchSubtrees: grow error"

    liftedClause i = liftVarsClause nVars $ (program p)!i
    nVars = (+ 1) <$> maxVarTree t

runResolution :: Program1 -> Goal1 ->
                 (Maybe [Halt TreeOper1], Derivation TreeOper1 Transition TreeOper1)
runResolution p g = runDerivation t f h
  where
    f = fmap (id *** matchTree p) . mguTransitions p
    h (_, _, u, _) _ = if successful u then ObservHalt u else ObservContinue
    t = matchTree p $ goalTree (Array.bounds $ program p) g

continueResolution :: Derivation TreeOper1 Transition TreeOper1 ->
                      (Maybe [Halt TreeOper1], Derivation TreeOper1 Transition TreeOper1)
continueResolution = runState derive

successful :: TreeOper1 -> Bool
successful = any hasSuccess . Array.elems . nodeBundleOper
  where
    hasSuccess (Right (Just ts)) = all final ts || all successful ts
    hasSuccess _                 = False

final :: TreeOper1 -> Bool
final = all finalB . Array.elems . nodeBundleOper
  where
    finalB (Right (Just ts)) = all final ts
    finalB (Right Nothing)   = True
    finalB _                 = False

data Guard = Guard
             {
               guardClause  :: Int
             , guardPath    :: Path
             , guardMeasure :: Term1
             }
           deriving (Eq, Generic)

instance Hashable Guard

data Invariant = Invariant
                {
                  invariantClause   :: Int
                , invariantMeasures :: HashSet (Path, Term1)
                }
              deriving (Eq)

data TransGuards = TransGuards
                   {
                     transPath   :: Path
                   , transSubst  :: Subst1
                   , transGuards :: HashSet Guard
                   , transLoops  :: [Term1Loop]
                   }

guardTransitions :: Program1 -> TreeOper1 -> [(TransGuards, TreeOper1)]
guardTransitions p t = cxt <$> mguTransitions p t
  where
    cxt (r, tMgu) = (TransGuards w s gs ciloops, tMgu)
      where
        gs       = HashSet.fromList $ (\(w1, b) -> Guard i w1 b) <$> ci
        s        = transitionSubst r
        w        = transitionPath r
        (v, i)   = (init &&& last) w
        a        = fromJust (t    `termAt` v)
        aMgu     = fromJust (tMgu `termAt` v)
        measures = snd <$> varReducts a aMgu
        subterms = nonVarSubterms $ clHead ((program p)!i)
        clProj   = (\m -> filter (\u -> isJust (snd u `matchMaybe` m)
                                 ) subterms
                   ) `concatMap` measures
        ciloops :: [Term1Loop]
        ciloops = filter (\(k, _, _) -> k == i) $ branchLoopsBy haveGuards w t
        cimeasures :: HashSet Term1
        cimeasures = HashSet.fromList $ snd <$>
                     ((\(_, a1, a2) -> recReducts a2 a1) `concatMap` ciloops)
        ci :: [(Path, Term1)]
        ci = (\m -> filter (\t' -> isJust (snd t' `matchMaybe` m)) clProj
             ) `concatMap` cimeasures
        haveGuards :: Rel Term1
        haveGuards x y = y /= goalHead && not (null (x `recReducts` y))

termAt :: TreeOper a -> Path -> Maybe a
termAt (NodeOper a _) []      = Just a
termAt (NodeOper _ b) (i:j:w) = nthOper j (b!i) >>= (`termAt` w)
termAt _              _       = Nothing

nthOper :: Int -> Oper [a] -> Maybe a
nthOper n (Right (Just ts)) = Just (ts!!n)
nthOper _ _                 = Nothing

runGuards :: Program1 -> TreeOper1 ->
             ( Maybe [Halt [Term1Loop]]
             , Derivation TreeOper1 TransGuards [Term1Loop] )
runGuards p t = runDerivation t (guardTransitions p . matchTree p) h
  where
    h ([(r, n)], _, u, _) d =
      if not (null l)
      then ObservHalt l
      else if HashSet.null ci
           then ObservBreak  -- Continue
           else if any (== ci) cxt
                then ObservCut
                else ObservContinue
      where
        l   = loops u
        e   = connect 0 n d
        ci  = transGuards r
        cxt = (\(_, _, r0) -> transGuards r0) <$> Graph.labEdges e
    h ([], 0, u, _) _ =
      if not (null l)
      then ObservHalt l
      else ObservContinue
      where
        l = loops u
    h _ _ = ObservContinue
    loops = findLoops . fst . runMatch p
    findLoops Nothing = []
    findLoops (Just outs) = concat $ catMaybes $ haltConditionMet <$> outs

continueGuards :: Derivation TreeOper1 TransGuards [Term1Loop] ->
                  ( Maybe [Halt [Term1Loop]]
                  , Derivation TreeOper1 TransGuards [Term1Loop] )
continueGuards = runState derive

resolutionLoops :: Program1 -> [Term1Loop]
resolutionLoops p =
  (findLoops . fst . runGuards p . t . Goal . \h -> [h]) `concatMap` heads
  where
    findLoops Nothing = []
    findLoops (Just outs) = concat $ catMaybes $ haltConditionMet <$> outs
    heads = clHead <$> (Array.elems $ program p)
    t = goalTree (Array.bounds $ program p)

guardedResolution :: Program1 -> Bool
guardedResolution = null . resolutionLoops
