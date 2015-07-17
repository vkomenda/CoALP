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
import Data.Graph.Inductive (Gr, Context, LEdge)
import qualified Data.Graph.Inductive as Graph
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.List (partition, delete, (\\))
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
         Left _           -> [( prefix ++ [i]
                              , clHead (liftedClause i) `mguMaybe` a)]
         _                -> []
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

--open :: TreeOper1 -> [Transition] -> [Path]
--open t rs = [w | w <- toBeUnified t [], w <- transitionPath <$> rs]

data Guard = Guard
             {
               guardClause  :: Int
             , guardPath    :: Path
             , guardMeasure :: Term1
             }
           deriving (Eq, Generic)

instance Hashable Guard

data TransGuards = TransGuards
                   {
                     transPath   :: Path
                   , transSubst  :: Subst1
                   , transGuards :: HashSet Guard
                   , transNew    :: [Path]
                   }

transOfEdge :: LEdge TransGuards -> TransGuards
transOfEdge (_, _, r) = r

guardTransitions :: Program1 -> TreeOper1 -> [(TransGuards, TreeOper1)]
guardTransitions p t = cxt <$> mguTransitions p tMatch
  where
    tMatch = matchTree p t
    cxt (r@(Transition w' s'), tMgu) = (TransGuards w' s' gs newNodePaths, tMgu)
      where
        gs = HashSet.fromList $ (\(i, v, b) -> Guard i v b) <$>
             (ci (transitionPath r) ++ ci `concatMap` newNodePaths)
        aMatch v = fromJust (tMatch `termAt` v)
        aMgu   v = fromJust (tMgu   `termAt` v)
        measures v = snd <$> varReducts (aMatch v) (aMgu v)
        subterms i  = nonVarSubterms $ clHead ((program p)!i)
        clProj i v =
          (\(v0, u) -> (i, v0, u)) <$>
          (\m -> (\u -> isJust (snd u `matchMaybe` m)
                 ) `filter` subterms i
          ) `concatMap` measures v
        tLeafNs      = leafPaths t
        tMatchLeafNs = leafPaths tMatch
        newNodePaths = tMatchLeafNs \\ tLeafNs
        ciloops :: Int -> Path -> [Term1Loop]
        ciloops i v = filter (\(k, _, _) -> k == i) $ bloops $ v ++ [i]
        bloops w = branchLoopsBy haveGuards w tMatch
        cimeasures :: Int -> Path -> HashSet Term1
        cimeasures i v =
          HashSet.fromList $ snd <$>
          ((\(_, a1, a2) -> recReducts a2 a1) `concatMap` ciloops i v)
        ci :: Path -> [(Int, Path, Term1)]
        ci w = (\m -> (\(_, _, u) -> isJust (u `matchMaybe` m)
                      ) `filter` clProj i v
               ) `concatMap` cimeasures i v
          where
            (v, i) = (init &&& last) w
        haveGuards :: Rel Term1
        haveGuards x y = y /= goalHead && not (null (x `recReducts` y))

siblingsGuards :: Context TreeOper1 TransGuards ->
                  Gr TreeOper1 TransGuards -> HashSet Guard
siblingsGuards ([(r, _)], _, _, _) e =
  if not (null sibInvariants) then head sibInvariants else HashSet.empty
  where
    sibInvariants = [s | s <- neSets, s `elem` delete s neSets]
    neSets = filter (not . HashSet.null) sibGuardsSets
    sibGuardsSets :: [HashSet Guard]
    sibGuardsSets = (\s -> HashSet.unions (guardsOf <$> s)) <$> siblings
    l = length $ transPath r
    ls = takeWhile (> 3) $ tail $ iterate (flip (-) 2) l
    siblings :: [[LEdge TransGuards]]
    siblings = siblingPathEdges <$> ls
    siblingPathEdges :: Int -> [LEdge TransGuards]
    siblingPathEdges k =
      filter ((== k) . length . transPath . transOfEdge) $ Graph.labEdges e
    guardsOf :: LEdge TransGuards -> HashSet Guard
    guardsOf = transGuards . transOfEdge
siblingsGuards _ _ = error "siblingsGuards: wrong arguments"

{-
pathCont :: TreeOper1 -> Path -> Path
pathCont (NodeOper _  bun) (i : j : w) = onFibre (bun!i)
  where
    onFibre (Right (Just ts)) = pathCont (ts!!j) w
    onFibre _ = w
pathCont _ []  = []
pathCont _ [i] = []

evenElems :: [a] -> [a]
evenElems []          = []
evenElems [a]         = []
evenElems (a : b : w) = b : evenElems w
-}

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
runGuards p t = runDerivation t (guardTransitions p) h
  where
    h c@([(r, n)], _, u, _) d =
      if not (null l)
      then ObservHalt l
      else if HashSet.null ci
           then if idemRenaming (transSubst r) &&
                   not (HashSet.null (siblingsGuards c e))
                then ObservCut
                else ObservContinue   -- Break
           else if any (== ci) cxt
                then ObservCut
                else ObservContinue
      where
        l   = loops u
        e   = connect 0 n d
        ci  = transGuards r
        cxt = (transGuards . transOfEdge) <$> Graph.labEdges e
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
