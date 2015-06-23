module CoALP.Resolution where

import Prelude hiding (all, any, elem, foldr, concat, concatMap, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst
import CoALP.Tree

import Control.Applicative
import Control.Arrow
import Data.Array ((!), (//))
import Control.Monad.Trans.State
import qualified Data.Array as Array
import Data.Foldable
import qualified Data.Graph.Inductive as Graph
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Ix (range)
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
                 (Maybe [Halt TreeOper1], Derivation TreeOper1)
runResolution p g = runDerivation (Array.bounds $ program p) g f h
  where
    f = mguTransitions p . matchTree p
    h t = if successful t then Just t else Nothing

continueResolution :: Derivation TreeOper1 ->
                      (Maybe [Halt TreeOper1], Derivation TreeOper1)
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

data GuardCxt = GuardCxt
                {
                  guardCxtClause :: Int
                , guardCxtSet    :: HashSet (Path, Term1)
                }
              deriving (Eq)

transitionGuards :: Program1 -> TreeOper1 -> [(Transition, TreeOper1, GuardCxt)]
transitionGuards p t = ctx <$> mguTransitions p t
  where
    ctx (r, t1) = (r, t1, GuardCxt (last w) $
                          let a  = t  `termAt` init w
                              a1 = t1 `termAt` init w
                          in
                           HashSet.fromList $ recVarReducts a1 a
                  )
      where
        w = transitionPath r

termAt :: TreeOper a -> Path -> a
termAt (NodeOper a _) [] = a
termAt (NodeOper _ b) (i:j:w) = termAt (nthOper j (b!i)) w
termAt _ w = error $ "termAt: invalid suffix " ++ show w

nthOper :: Int -> Oper [a] -> a
nthOper n (Right (Just ts)) = ts!!n
nthOper n _ = error $ "nthOper: missing term " ++ show n

singletonDerivation :: TreeOper1 ->
                       (TreeOper1 -> [(Transition, TreeOper1)]) ->
                       (TreeOper1 -> Maybe v) ->
                       Derivation v
singletonDerivation t f h =
  Derivation
  {
    derivation        = Graph.mkGraph [(0, t)] []
  , derivationTrees   = HashMap.singleton t 0
  , derivationQueue   = [0]
  , derivationStep    = f
  , derivationHalt    = h
  , derivationMaxSize = 1000
  }

runSingletonMatch :: Program1 -> TreeOper1 ->
                     (Maybe [Halt [Term1Loop]], Derivation [Term1Loop])
runSingletonMatch p t =
  runState derive $ singletonDerivation t (matchTransitions p) h
  where
    h t1 = if null l then Nothing else Just l
      where l = loops t1
    loops = treeLoopsBy $ \a1 a2 -> a2 /= goalHead && not (a1 `recReduct` a2)

resolutionLoops :: Program1 -> [Term1Loop]
resolutionLoops p = concat $ go [] <$> (goalTree bounds <$> goals)
  where
    go :: [GuardCxt] -> TreeOper1 -> [Term1Loop]
    go gcxt t
      | not (null loops) = loops
      | otherwise = concat $ (\(_, t1, c) ->
                               if c `elem` gcxt
                               then []
                               else go (c : gcxt) t1
                             ) <$> guards
      where
        guards = (transitionGuards liftedP . matchTree liftedP) t
        nVars = (+ 1) <$> maxVarTree t
        loops = findLoops $ fst $ runSingletonMatch liftedP t
        liftedP = liftedBy nVars
    findLoops Nothing = []
    findLoops (Just outs) = concat $ catMaybes $ haltConditionMet <$> outs
    goals = (\h -> Goal [h]) <$> heads
    heads = clHead <$> (Array.elems $ program p)
    liftedBy n = Program $ Array.listArray bounds $ liftedClause n <$> range bounds
    liftedClause n i = liftVarsClause n $ (program p)!i
    bounds = Array.bounds $ program p

guardedResolution :: Program1 -> Bool
guardedResolution = null . resolutionLoops
