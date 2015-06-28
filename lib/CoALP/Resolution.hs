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
import Data.Array ((!), (//))
import Control.Monad.Trans.State
import qualified Data.Array as Array
import Data.Foldable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List (partition)
import Data.Maybe

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
    h u = if successful u then Just u else Nothing
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
               guardClause   :: Int
             , guardMeasures :: HashSet Term1
             }
           deriving (Eq)

data GuardCxt = GuardCxt
                {
                  guardCxtClause   :: Int
                , guardCxtMeasures :: HashSet (Path, Term1)
                }
              deriving (Eq)

transitionGuards :: Program1 -> TreeOper1 -> [(Transition, TreeOper1, GuardCxt)]
transitionGuards p t = cxt <$> mguTransitions p t
  where
    cxt (r, tMgu) = (r, tMgu, GuardCxt i clProj)
      where
        w        = transitionPath r
        (v, i)   = (init &&& last) w
        aMatch   = fromJust (t    `termAt` v)
        aMgu     = fromJust (tMgu `termAt` v)
        measures = HashSet.fromList $ snd <$> varReducts aMatch aMgu
        subterms = nonVarSubterms $ clHead ((program p)!i)
        clProj   = HashSet.unions $
                   (\m -> HashSet.fromList $
                          filter (\s -> isJust (snd s `matchMaybe` m)
                                 ) subterms
                   ) <$> HashSet.toList measures

guardCxt :: GuardCxt -> TreeOper1 -> GuardCxt
guardCxt (GuardCxt i gs) t =
  GuardCxt i $
  HashSet.fromList $ filter
  (\g -> any (isJust . matchMaybe (snd g)) $ HashSet.toList $ loopGuardTerms
  ) $ HashSet.toList gs
  where
    loopGuardTerms :: HashSet Term1
    loopGuardTerms = HashSet.unions $ snd <$> loopGuards
    loopGuards :: [(Int, HashSet Term1)]
    loopGuards = loopGuard <$> guardedLoops
    loopGuard :: Term1Loop -> (Int, HashSet Term1)
    loopGuard (j, b, a) = (j, HashSet.fromList $ snd <$> a `recVarReducts` b)
    guardedLoops :: [Term1Loop]
    guardedLoops = (\(j,_,_) -> i == j) `filter` treeLoopsBy haveGuards t
    haveGuards :: Rel Term1
    haveGuards x y = y /= goalHead && not (null (x `recVarReducts` y))

termAt :: TreeOper a -> Path -> Maybe a
termAt (NodeOper a _) []      = Just a
termAt (NodeOper _ b) (i:j:w) = nthOper j (b!i) >>= (`termAt` w)
termAt _              _       = Nothing

nthOper :: Int -> Oper [a] -> Maybe a
nthOper n (Right (Just ts)) = Just (ts!!n)
nthOper _ _                 = Nothing

resolutionLoops :: Program1 -> [Term1Loop]
resolutionLoops p = concat $ go [] <$> (goalTree bounds <$> goals)
  where
    go :: [GuardCxt] -> TreeOper1 -> [Term1Loop]
    go gcxts t
      | not (null loops) = loops
      | otherwise = onClauseProj `concatMap` clauseProj
      where
        onClauseProj (_, u, c) =
          if HashSet.null $ guardCxtMeasures gcxt
          then go gcxts u
          else
            if gcxt `elem` gcxts
            then []
            else go (gcxt : gcxts) u
          where
            gcxt = guardCxt c tMatch
        clauseProj = transitionGuards p tMatch
        tMatch = matchTree p t
        loops = findLoops $ fst $ runMatch p t
    findLoops Nothing = []
    findLoops (Just outs) = concat $ catMaybes $ haltConditionMet <$> outs
    goals = (\h -> Goal [h]) <$> heads
    heads = clHead <$> (Array.elems $ program p)
    bounds = Array.bounds $ program p

guardedResolution :: Program1 -> Bool
guardedResolution = null . resolutionLoops
