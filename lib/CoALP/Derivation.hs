module CoALP.Derivation where

import Prelude hiding (foldr, concatMap, all, sequence, sequence_)

import Control.Applicative
import Control.Monad.Trans.State
import Data.Hashable
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Graph.Inductive (Gr, Node, Context, (&))
import qualified Data.Graph.Inductive as Graph
import Data.List (nub)
import Data.Maybe
import Data.Traversable

data Observ v = ObservContinue
              | ObservCut
              | ObservHalt v
              deriving Show

data Hashable n => Derivation n e v =
  Derivation
  {
    -- | derivation graph
    derivation        :: Gr n e
    -- | bijection from found data to graph nodes
  , derivationNodes   :: HashMap n Node
    -- | work queue
  , derivationQueue   :: [Node]
    -- read-only environment - TODO
    -- | step function
  , derivationStep    :: n -> [(e, n)]
    -- | continuation condition with output of type @v@
  , derivationObserv  :: Context n e -> Gr n e -> Observ v
    -- | maximum number of nodes in the graph
  , derivationMaxSize :: Int
  }

initDerivation :: Hashable n => n -> (n -> [(e, n)]) ->
                  (Context n e -> Gr n e -> Observ v) ->
                  Derivation n e v
initDerivation t f h =
  Derivation
  {
    derivation        = Graph.mkGraph [(0, t)] []
  , derivationNodes   = HashMap.singleton t 0
  , derivationQueue   = [0]
  , derivationStep    = f
  , derivationObserv  = h
  , derivationMaxSize = 10000
  }

data Halt v = HaltNodeNotFound Node
            | HaltMaxSizeExceeded
            | HaltConditionMet v
            deriving (Show, Eq)

haltConditionMet :: Halt v -> Maybe v
haltConditionMet (HaltConditionMet v) = Just v
haltConditionMet _ = Nothing

runDerivation :: (Eq n, Hashable n) => n -> (n -> [(e, n)]) ->
                 (Context n e -> Gr n e -> Observ v) ->
                 (Maybe [Halt v], Derivation n e v)
runDerivation t f h = runState (observ0 $ h ([], 0, t, []) $ derivation d) d
  where
    observ0 (ObservHalt v) = return $ Just [HaltConditionMet v]
    observ0 ObservCut      = return Nothing
    observ0 ObservContinue = derive
    d = initDerivation t f h

derive :: (Eq n, Hashable n) => State (Derivation n e v) (Maybe [Halt v])
derive = do
  d <- gets derivation
  q <- gets derivationQueue
  case q of
   [] -> return Nothing
   n:_ -> do
     case Graph.lab d n of
      Nothing -> return $ Just [HaltNodeNotFound n]
      Just t -> do
        f <- gets derivationStep
        outs <- sequence $ queueBreadthFirst n <$> f t
        modify $ \st -> st { derivationQueue = tail $ derivationQueue st }
        let leftouts = filter isJust outs
        if null leftouts
          then derive
          else return $ sequence leftouts

queueBreadthFirst :: (Eq n, Hashable n) => Node -> (e, n) ->
                     State (Derivation n e v) (Maybe (Halt v))
queueBreadthFirst n (r, t) = do
  ts <- gets derivationNodes
  -- check if a copy of the same tree has been searched already
  case HashMap.lookup t ts of  -- TODO (there are still some semantic copies):
                               -- 1. relate trees with the same success subtrees
                               -- 2. equiv. up to variable renaming
                               -- 3. 1&2 possible using NF conversion before
                               --    adding trees to derivation
   Nothing -> do
     m <- gets derivationMaxSize
     if n < m
       then do
         d <- gets derivation
         let i = Graph.noNodes d
             cxt = ([(r, n)], i, t, [])
         modify $ \st ->
           st { derivation = cxt & derivation st
              , derivationNodes = HashMap.insert t i $ derivationNodes st }
         h <- gets derivationObserv
         -- check the halting condition
         case h cxt d of
          ObservContinue -> do
            -- queue an intermediate node for further search
            modify $ \st ->
              st { derivationQueue = derivationQueue st ++ [i] }
            return Nothing
          ObservCut ->
            -- do not queue the last node in a cut branch node for further
            -- however, continue with the derivation
            return Nothing
          ObservHalt v  ->
            -- do not queue a halting node for further search
            return $ Just $ HaltConditionMet v
       else return $ Just HaltMaxSizeExceeded
   Just j -> do
     modify $ \st ->
       st { derivation = ([(r, n)], j, t, []) & derivation st }
     return Nothing

nodePaths :: Node -> Node -> Gr a b -> [[Node]]
nodePaths start = go [start] start
  where
    go visited i j g
      | i == j    = [[]]
      | otherwise = [ k : path
                    | k <- nub $ Graph.suc g i
                    , k `notElem` visited
                    , path <- go (k : visited) k j g
                    ]

nodesClosedBy :: Node -> Node -> Gr a b -> IntSet
nodesClosedBy start end g =
  IntSet.fromList (start : concat (nodePaths start end g))

connect :: Node -> Node -> Gr a b -> Gr a b
connect start end g = Graph.ufold betw Graph.empty g
  where
    betw (adjin, i, a, adjout) g'
      | not (IntSet.member i ns) = g'
      | otherwise = (es adjin, i, a, es adjout) & g'
    ns = nodesClosedBy start end g
    es = filter (\(_, i) -> IntSet.member i ns)
