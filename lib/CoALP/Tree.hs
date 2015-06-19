{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module CoALP.Tree where

import Prelude hiding (foldr, concat, concatMap, all, sequence, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst

import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.State
import Data.Array (Array, (!), (//))
import qualified Data.Array as Array
import Data.Foldable
import Data.Hashable
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Graph.Inductive (Gr, Node, (&))
import qualified Data.Graph.Inductive as Graph
import Data.List (partition)
import Data.Maybe
import Data.Traversable

import GHC.Generics (Generic)

{-
-- | Lazily evaluated possibly infinite tree.
data Tree a = Node
              {
                nodeTerm :: a
              , nodeBundle :: Array Int (Maybe [Tree a])
              }
            deriving (Show, Eq)

-- | Computation of the set of loops for the guardedness check 2.
treeLoopsBy :: Ord a => Rel a -> Tree a -> Set (a, a)
treeLoopsBy rel = treeLoopsBy' rel Set.empty Set.empty

treeLoopsBy' :: Ord a => Rel a -> Set (Int, a) -> Set (a, a) ->
                Tree a -> Set (a, a)
treeLoopsBy' rel termsAbove knownLoops (Node a bun) =
  foldr (\(i, mt) loops1 ->
          case mt of
           Nothing -> loops1
           Just body -> foldr (\b loops2 ->
                                treeLoopsBy' rel
                                  ((i, a) `Set.insert` termsAbove)
                                  loops2 b
                              ) (foundLoops i `Set.union` loops1) body
        ) knownLoops (Array.assocs bun)
  where
    related i = Set.filter (\(j, b) -> i == j && a `rel` b) termsAbove
    foundLoops i = Set.map (\(_, b) -> (b, a)) $ related i

type Term0 = Char

example_pq :: Tree Term0
example_pq =
  Node 'p' (
    Array.array (0, 1)
    [ (0, Just [
          Node 'q' (
             Array.array (0, 1)
             [ (0, Nothing)
             , (1, Just [
                   Node 'p' (
                      Array.array (0, 1)
                      [ (0, Just
                            [ Node 'q' (
                                 Array.array (0, 1)
                                 [ (0, Nothing)
                                 , (1, undefined) ]
                                 ) ]
                        )
                      , (1, Nothing) ]
                      ) ]
               ) ]
             ) ]
      )
    , (1, Nothing)
    ] )
-}

-- | Operational notion of a tree continuation on strictly evaluated bundles.
data TBC = ToBeMatched | ToBeUnified
         deriving (Eq, Ord, Generic)

instance Hashable TBC

type Oper v = Either TBC (Maybe v)

-- | Operational tree with strictly evaluated bundles.
data TreeOper a =
  NodeOper
  {
    nodeTermOper :: a
  , nodeBundleOper :: Array Int (Oper [TreeOper a])
  }
  deriving (Eq, Generic)

instance (Array.Ix i, Hashable i, Hashable e) => Hashable (Array i e) where
  hashWithSalt salt a = salt `hashWithSalt` Array.assocs a

instance Hashable a => Hashable (TreeOper a)

type TreeOper1 = TreeOper Term1

instance Functor TreeOper where
  fmap f (NodeOper a b) = NodeOper (f a) $ (fmap.fmap.fmap.fmap.fmap) f b

instance Foldable TreeOper where
  foldr f z (NodeOper a b) = f a $ (r.r.r.r.r) f b z
    where
      r :: Foldable t => (a -> b -> b) -> t a -> b -> b
      r = flip . foldr

instance Traversable TreeOper where
  traverse f (NodeOper a b) =
    NodeOper <$> f a <*> (traverse.traverse.traverse.traverse.traverse) f b

maxVarTree :: TreeOper1 -> Maybe Int
maxVarTree = foldr (max . maxVarTerm) Nothing

initTree :: (Int, Int) -> Term1 -> TreeOper1
initTree bounds a =
  NodeOper a $ Array.listArray bounds (repeat $ Left ToBeMatched)

matchTree :: Program1 -> TreeOper1 -> TreeOper1
matchTree p (NodeOper a b) =
  NodeOper a $ Array.listArray (Array.bounds b) (grow <$> Array.assocs b)
  where
    grow :: (Int, Oper [TreeOper1]) -> Oper [TreeOper1]
    grow (_, (Right (Just ts)))  = Right $ Just (matchTree p <$> ts)
    grow (i, (Left ToBeMatched)) =
      case clHead c `matchMaybe` a of
       Nothing -> Left ToBeUnified
       Just s  -> Right $ Just (matchTree p <$>
                                initTree (Array.bounds $ program p) <$>
                                (>>= subst s) <$>
                                clBody c)
      where
        c = (program p)!i
    grow oper = snd oper

type Rel a = a -> a -> Bool

-- | Computation of the set of loops for the guardedness check 2.
treeLoopsBy :: (Eq a, Hashable a) => Rel a -> TreeOper a -> [(a, a)]
treeLoopsBy rel = treeLoopsBy' rel [] []

treeLoopsBy' :: (Eq a, Hashable a) => Rel a -> [(Int, a)] -> [(a, a)] ->
                TreeOper a -> [(a, a)]
treeLoopsBy' rel termsAbove knownLoops (NodeOper a bun) =
  foldr onFibres knownLoops (Array.assocs bun)
  where
    related i = filter (\(j, b) -> i == j && a `rel` b) $ termsAbove
    foundLoops i = (\(_, b) -> (b, a)) <$> related i
    onFibres (_, Right Nothing) loops1 = loops1
    onFibres (i, Right (Just body)) loops1 =
      foldr (\b loops2 -> treeLoopsBy' rel ((i, a) : termsAbove) loops2 b
            ) (foundLoops i ++ loops1) body
    onFibres (_, Left _) loops1 = loops1

type Path = [Int]

data Transition = Transition
                  {
                    transitionPath  :: Path
                  , transitionSubst :: Subst1
                  }

data Derivation v =
  Derivation
  {
    -- | derivation graph
    derivation        :: Gr TreeOper1 Transition
    -- | bijection from found trees to nodes
  , derivationTrees   :: HashMap TreeOper1 Node
    -- | work queue
  , derivationQueue   :: [Node]
    -- read-only environment - TODO
    -- | step function
  , derivationStep    :: TreeOper1 -> [(Transition, TreeOper1)]
    -- | halting condition
  , derivationHalt    :: TreeOper1 -> Maybe v
    -- | maximum number of nodes in the graph
  , derivationMaxSize :: Int
  }

initDerivation :: (Int, Int) -> Term1 ->
                  (TreeOper1 -> [(Transition, TreeOper1)]) ->
                  (TreeOper1 -> Maybe v) ->
                  Derivation v
initDerivation bounds a f h =
  Derivation
  {
    derivation        = Graph.mkGraph [(0, t)] []
  , derivationTrees   = HashMap.singleton t 0
  , derivationQueue   = [0]
  , derivationStep    = f
  , derivationHalt    = h
  , derivationMaxSize = 10000
  }
  where
    t = initTree bounds a

data Halt v = HaltNodeNotFound Node
            | HaltMaxSizeExceeded
            | HaltConditionMet v
            deriving (Show, Eq)

type Term1Loop = (Term1, Term1)

success :: Either a ()
success = Right ()

runDerivation :: (Int, Int) -> Term1 ->
                 (TreeOper1 -> [(Transition, TreeOper1)]) ->
                 (TreeOper1 -> Maybe v) ->
                 (Either (Halt v) (), Derivation v)
runDerivation bounds a f h = runState derive $ initDerivation bounds a f h

derive :: State (Derivation v) (Either (Halt v) ())
derive = do
  d <- gets derivation
  q <- gets derivationQueue
  case q of
   [] -> return success
   n:_ -> do
     m <- gets derivationMaxSize
     if n < m
       then
         case Graph.lab d n of
          Nothing -> return $ Left $ HaltNodeNotFound n
          Just t -> do
            f <- gets derivationStep
            sequence_ $ queueBreadthFirst n <$> f t
            modify $ \st -> st { derivationQueue = tail $ derivationQueue st }
            h <- gets derivationHalt
            case h t of
             Nothing -> derive
             Just v  -> return $ Left $ HaltConditionMet v
       else return $ Left HaltMaxSizeExceeded

queueBreadthFirst :: Node -> (Transition, TreeOper1) -> State (Derivation v) ()
queueBreadthFirst n (r, t) = do
  ts <- gets derivationTrees
  case HashMap.lookup t ts of    -- FIXME: equiv. up to variable renaming
   Nothing -> do
     d <- gets derivation
     let i = Graph.noNodes d
     modify $ \st ->
       st { derivation = ([(r, n)], i, t, []) & derivation st
          , derivationTrees = HashMap.insert t i $ derivationTrees st
          , derivationQueue = derivationQueue st ++ [i] }
   Just j -> do
     modify $ \st ->
       st { derivation = ([(r, n)], j, t, []) & derivation st }

matchTransitions :: Program1 -> TreeOper1 -> [(Transition, TreeOper1)]
matchTransitions p t = growSuccessful $ failedAndSuccessful $ atBoundary [] t
  where
    growSuccessful :: ([Path], [(Path, Subst1)]) -> [(Transition, TreeOper1)]
    growSuccessful (pts, trs) =
      (\(w, s) -> (Transition w s, grow (Just s) w $ noMatch pts)) <$> trs

    noMatch :: [Path] -> TreeOper1
    noMatch = foldr (grow Nothing) t

    failedAndSuccessful :: [(a, Maybe b)] -> ([a], [(a, b)])
    failedAndSuccessful =
      (map fst *** map (id *** fromJust)) . partition (isNothing . snd)

    atBoundary :: Path -> TreeOper1 -> [(Path, Maybe Subst1)]
    atBoundary prefix (NodeOper a b) =
      (\(i, oper) ->
        case oper of
         Right (Just ts)  -> (\(j, u) -> atBoundary (prefix ++ [i, j]) u
                             ) `concatMap` (zip [0..] ts)
         Left ToBeMatched -> [( prefix ++ [i]
                              , clHead ((program p)!i) `matchMaybe` a)]
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
        o | isNothing ms = Left ToBeUnified
          | otherwise    = Right $ Just tbs
        tbs = initTree (Array.bounds $ program p) <$>
              (>>= subst (fromJust ms)) <$> clBody ((program p)!i)
    grow _ _ _ = error "matchSubtrees: grow error"

runMatch :: Program1 -> Term1 ->
            (Either (Halt [Term1Loop]) (), Derivation [Term1Loop])
runMatch p a = runDerivation (Array.bounds $ program p) a (matchTransitions p) h
  where
    h t = if null l then Nothing else Just l
      where l = loops t
    loops = treeLoopsBy $ \a1 a2 -> not (a1 `recReduct` a2)

-- | Implementation of Tier 2 guardedness check.
--
-- @matchLoops p@ is empty when the program @p@ is guarded by the Tier 2 check.
--
-- @matchLoops p@ equals @loops@ when the incremental loop search procedure
-- halted with output @loops@, which may not necessarily contain the set of all
-- loops in the program @p@. If more loops need to be found, 'runMatch' can be
-- used iteratively by reapplication to the halted state to yield further loops
-- if there are any.
matchLoops :: Program1 -> [Term1Loop]
matchLoops p = concat $ findLoops <$> runMatch p <$> heads
  where
    findLoops (Left (HaltConditionMet v), _) = v
    findLoops _ = []
    heads = clHead <$> (Array.elems $ program p)

guardedMatch :: Program1 -> Bool
guardedMatch = null . matchLoops
