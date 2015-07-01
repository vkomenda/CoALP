module CoALP.Derivation where

import Prelude hiding (foldr, concat, concatMap, all, sequence, sequence_)

import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.State
import Data.Array (Array, (!), (//))
import qualified Data.Array as Array
import Data.Hashable
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Graph.Inductive (Gr, Node, (&))
import qualified Data.Graph.Inductive as Graph
import Data.Maybe
import Data.Traversable

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
    -- | halting condition with output of type @v@
  , derivationHalt    :: n -> Maybe v
    -- | maximum number of nodes in the graph
  , derivationMaxSize :: Int
  }

initDerivation :: Hashable n => n -> (n -> [(e, n)]) -> (n -> Maybe v) ->
                  Derivation n e v
initDerivation t f h =
  Derivation
  {
    derivation        = Graph.mkGraph [(0, t)] []
  , derivationNodes   = HashMap.singleton t 0
  , derivationQueue   = [0]
  , derivationStep    = f
  , derivationHalt    = h
  , derivationMaxSize = 10000
  }

data Halt v = HaltNodeNotFound Node
            | HaltMaxSizeExceeded
            | HaltConditionMet v
            deriving (Show, Eq)

haltConditionMet :: Halt v -> Maybe v
haltConditionMet (HaltConditionMet v) = Just v
haltConditionMet _ = Nothing

runDerivation :: (Eq n, Hashable n) => n -> (n -> [(e, n)]) -> (n -> Maybe v) ->
                 (Maybe [Halt v], Derivation n e v)
runDerivation t f h = runState derive $ initDerivation t f h

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
         modify $ \st ->
           st { derivation = ([(r, n)], i, t, []) & derivation st
              , derivationNodes = HashMap.insert t i $ derivationNodes st }
         h <- gets derivationHalt
         -- check the halting condition
         case h t of
          Just v  -> do
            -- do not queue a halting node for further search
            return $ Just $ HaltConditionMet v
          Nothing -> do
            modify $ \st ->
              st { derivationQueue = derivationQueue st ++ [i] }
            return Nothing
       else return $ Just HaltMaxSizeExceeded
   Just j -> do
     modify $ \st ->
       st { derivation = ([(r, n)], j, t, []) & derivation st }
     return Nothing
