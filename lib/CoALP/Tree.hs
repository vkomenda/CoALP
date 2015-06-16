{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module CoALP.Tree where

import Prelude hiding (foldr, concatMap, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst

import Control.Applicative
import Control.Monad.Trans.State
import Data.Array (Array, (!), (//))
import qualified Data.Array as Array
import Data.Foldable
import Data.Hashable
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Graph.Inductive (Gr, Node, (&))
import qualified Data.Graph.Inductive as Graph
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

type Oper a = Either TBC (Maybe a)

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

unguardedMatchLoops :: Program1 -> Int -> [(Term1, Term1)]
unguardedMatchLoops p i =
  treeLoopsBy (\a b -> not (a `recReduct` b)) $
  matchTree p $
  initTree (Array.bounds $ program p) (clHead c)
  where
    c = (program p)!i

type Path = [Int]

data Transition = Transition
                  {
                    transitionPath  :: Path
                  , transitionSubst :: Maybe Subst1
                  }

data Derivation = Derivation
                  {
                    -- | derivation graph
                    derivation        :: Gr TreeOper1 Transition
                    -- | bijection from found trees to nodes
                  , derivationTrees   :: HashMap TreeOper1 Node
                    -- | work queue
                  , derivationQueue   :: [Node]
                    -- | read-only environment - TODO
                  , derivationFun     :: TreeOper1 -> [(Transition, TreeOper1)]
                  , derivationMaxSize :: Int
                  }

initDerivation :: (Int, Int) -> Term1 ->
                  (TreeOper1 -> [(Transition, TreeOper1)]) ->
                  Derivation
initDerivation bounds a f =
  Derivation
  {
    derivation        = Graph.mkGraph [(0, t)] []
  , derivationTrees   = HashMap.singleton t 0
  , derivationQueue   = [0]
  , derivationFun     = f
  , derivationMaxSize = 100
  }
  where
    t = initTree bounds a

data DErr = DErrNodeNotFound Node
          | DErrMaxSizeExceeded
          deriving Show

success :: Either a ()
success = Right ()

runDerivation :: (Int, Int) -> Term1 ->
                 (TreeOper1 -> [(Transition, TreeOper1)]) ->
                 (Either DErr (), Derivation)
runDerivation bounds a f = runState derive $ initDerivation bounds a f

derive :: State Derivation (Either DErr ())
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
          Nothing -> return $ Left $ DErrNodeNotFound n
          Just t -> do
            f <- gets derivationFun
            sequence_ $ queueBreadthFirst n <$> f t
            modify $ \st -> st { derivationQueue = tail $ derivationQueue st }
            derive
       else return $ Left DErrMaxSizeExceeded

queueBreadthFirst :: Node -> (Transition, TreeOper1) ->
                     State Derivation (Either DErr ())
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
     return success
   Just j -> do
     modify $ \st ->
       st { derivation = ([(r, n)], j, t, []) & derivation st }
     return success

matchSubtrees :: Program1 -> TreeOper1 -> [(Transition, TreeOper1)]
matchSubtrees p t = go t []
  where
    go :: TreeOper1 -> Path -> [(Transition, TreeOper1)]
    go (NodeOper a b) prefix =
      (\(i, oper) ->
        case oper of
         Right (Just ts)  -> (\(j, u) -> go u (prefix ++ [i, j])
                             ) `concatMap` (zip [0..] ts)
         Left ToBeMatched -> [(Transition w ms, grow w t)]
           where
             w = prefix ++ [i]
             ms = clHead c `matchMaybe` a
             c = (program p)!i

             grow :: Path -> TreeOper1 -> TreeOper1
             grow (k:l:u) (NodeOper a0 b0) =
               NodeOper a0 $ b0 // [(k,
                                     case b0!k of
                                      Right (Just tbs) ->
                                        Right $ Just $
                                        take l tbs ++ grow u (tbs!!l) :
                                        drop (l+1) tbs
                                      _ -> error "matchSubtrees: invalid path"
                                           -- TODO: return
                                    )]
             grow [k] (NodeOper a0 b0)
               | isNothing ms = NodeOper a0 $ b0 // [(k, Right Nothing)]
               | otherwise    = NodeOper a0 $ b0 // [(k, Right $ Just tbs)]
               where
                 tbs :: [TreeOper1]
                 tbs = initTree (Array.bounds $ program p) <$>
                       (>>= subst (fromJust ms)) <$> clBody c
             grow _ _ = error "matchSubtrees: grow error"

         _ -> []
      ) `concatMap` (Array.assocs b)

runMatch :: Program1 -> Term1 -> (Either DErr (), Derivation)
runMatch p a = runState derive $
               initDerivation (Array.bounds $ program p) a $
               matchSubtrees p
