module CoALP.Guards2 where

import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.CTree
import CoALP.Substitution
import CoALP.CoInTree
import CoALP.Process
import CoALP.UI.Printer


import Control.Monad.State.Lazy
import Data.Functor.Identity
import Data.Maybe
import Data.List 
import           Data.Map (Map)
import qualified Data.Map as Map

type GCDetails = (XSubst,DSet,[TermTree])

dummyDS = initDS

dummyGCDetails = (dummyXSubst, dummyDS, [])

saveGCs :: String -> [(Bool, GCDetails)] -> IO ()
saveGCs id results =
  let trees = map (coTree' . snd3 . snd) results
  in  saveCoIn id 0 trees 

drawGCs :: [(Bool, GCDetails)] -> IO ()
drawGCs results =
  putStrLn $ concat $ map (drawGC) results

drawGC :: (Bool, GCDetails) -> String
drawGC (result,(subs,ds,checked))
  | result = show result
  | otherwise = "\n" ++ show result ++
      "\nSubstitution: " ++ show0 subs ++ 
      "\nClause: " ++ clauseTreeToString clause ++      
      "\nGC Checked 0: " ++ termTreeToString (checked !! 0) ++ 
      "\nGC Checked 1: " ++ termTreeToString (checked !! 1)
    where clause = (prg' ds) !! ((fst subs) - 1)

--guarded :: Program -> [String] -> (Bool, [String])
--guarded prog cm
--  | (fst $ head gc1Result) == False = (False, ["GC1 unguarded"] ++ (map (termTreeToString) $ (concat $ map snd gc1Result)) ) 
--  | (fst $ head gc2Result) == False = (False, ["GC2 unguarded"] ++ (map (drawGC) gc2Result) )
--  | (fst $ head gc3Result) == False = (False, ["GC3 unguarded"] ++ (map (drawGC) gc3Result) )
--  | otherwise = (True, [])
--  where gc1Result = gc1Prog prog
--        gc2Result = gc2Prog prog
--        gc3Result = gc3Prog prog cm

--------------------------------------------------------------------------------
---------------------------------------GC1--------------------------------------
--------------------------------------------------------------------------------

constantGuard :: TermTree -> TermTree -> Bool
constantGuard t0 t1 =
  let disTree = pairTree t0 t1
  in  Map.foldl (||) False (Map.map (funcDisagrement) (mapping disTree))

funcDisagrement :: (String,String) -> Bool
funcDisagrement (a,b) 
  | a == b = False
  | isVariable a = False
  | isVariable b = False
  | otherwise = True

corecursiveReduct :: TermTree -> TermTree -> Bool
corecursiveReduct t0 t1 =
  let disTree = pairTree t0 t1
      disMap = Map.filter (\(a,b) -> a /= b) (mapping disTree)
      funcVarMap = Map.filter (\(a,b) -> (not $ isVariable a) && (isVariable b)) disMap
      domains = Map.keys funcVarMap
      subTrees = map (ee . getSubCTree t0) domains
      t1Values = map (snd) $ Map.elems funcVarMap
      exists = map (\(t,s) -> containsValue s t) (zip subTrees t1Values)
  in  or exists

gc1 :: TermTree -> TermTree -> (Bool, [TermTree])
gc1 t0 t1 = 
  if constantGuard t0 t1 || corecursiveReduct t0 t1
  then (True, [])
  else (False, (t0:t1:[]))


gc1Items :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, [TermTree])]
gc1Items (prg,_,_) = gc1Prog prg

gc1Prog :: Program -> [(Bool, [TermTree])]
gc1Prog prg = 
  let gc1ed = map gc1Clause prg
      result = and $ map (fst) (concat gc1ed)
  in  if  result
      then [(True, [])]
      else filter (\(a,_) -> not a) (concat gc1ed)

gc1Clause :: ClauseTree -> [(Bool, [TermTree])]
gc1Clause ct = 
  let terms = termsWithHead ct
      gc1ed = map (gc1 (clHead ct)) terms
      result
        | terms == [] = True
        | otherwise   = and $ map (fst) gc1ed
  in  if result
      then [(True,[])]
      else filter (\(a,_) -> not a) gc1ed


--boolMap = Map.map (\(a,b) -> a == b) m

--------------------------------------------------------------------------------
---------------------------------------GC2--------------------------------------
--------------------------------------------------------------------------------

-- Takes a  cotree and a termtree and returns all instances of that predicate in the goal tree along with their domain
repeatedPredicate :: CoInTree -> TermTree -> [([Int],TermTree)]
repeatedPredicate ct tt = 
  let pred = tHead tt
      matches = Map.map (fromJust . fromTT) (Map.filter (sameTTRoot pred) (mapping ct))
  in  Map.toList matches

sameTTRoot v (TT a) = sameAsRoot v a
sameTTRoot _ _ = False

-- Takes a working set and returns the instances that the predicate appears
gc2DSRepeatPred :: DSet -> [([Int],TermTree)]
gc2DSRepeatPred (DS {coTree' = ct}) =
  let predicate = fromJust $ Map.lookup [1] (mapping ct)
  in  repeatedPredicate ct (fromJust $ fromTT predicate)

repeatedClause :: CoInTree -> Int -> [[Int]]
repeatedClause ct n =
  let matches = Map.filter (subsOfClause n) (mapping ct)
  in  Map.keys matches

subsOfClause n (XSub a) =
  if (fst a) == n
  then True
  else False
subsOfClause _ _ =  False

getTerms :: CoInTree -> [[Int]] ->  [([Int],TermTree)]
getTerms ct@(CTree _ _ m) ds =
  let terms = map (fromJust . (flip Map.lookup m)) (map init ds)
      lastDs = lastDomains ds
      extraDs = concat $ map (flip sharedPredChild ct) lastDs 
      extraTerms = map (fromJust . (flip Map.lookup m)) extraDs
  in  zip ds (map (fromJust . fromTT) terms) ++ zip extraDs (map (fromJust . fromTT) extraTerms)

gc2PairwiseAux :: DSet -> [([Int],TermTree)] -> [(Bool, GCDetails)]
gc2PairwiseAux ds reps =
  let gc1pairwise = map (gc2Pairwise'' ds reps) reps
      result = and $ map (fst) (concat gc1pairwise)
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat gc1pairwise)

gc2Pairwise'' :: DSet ->  [([Int],TermTree)] -> ([Int],TermTree) -> [(Bool, GCDetails)]
gc2Pairwise'' ds@(DS {coTree' = ct, prg' = prog}) reps rep@(d,t) =
  let filtered = filter (\(a,b) -> d `isPrefixOf` a && d /= a) reps
      gc1ed = map ((gc1 t) . snd) filtered -- [(Bool, [TermTree])]
      result = and $ map (fst) gc1ed
      merged = zip (map fst filtered) gc1ed
      rearrage = map (\(a,(b,c)) -> (b, (fromJust $ fromXSub $ fromJust $ getCoIn a, c))) merged
      getCoIn = flip Map.lookup (mapping ct)
      replace = map (\(a, (b,c)) -> (a, ( b, ds, c))) rearrage	
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) replace


reformulateTerms :: (Int,[([Int],TermTree)]) -> [(Int, ([Int],TermTree))]
reformulateTerms (a,b) = map (\(c,d) -> (a,(c,d))) b 


gc2Aux :: [DSet] -> [DSet] -> [(Bool, GCDetails)]
gc2Aux []   _    = [(True, dummyGCDetails)]
gc2Aux curr prev =
  let gc2Curr = map (gc2DSSameClause) curr
      result = and $ map (fst) (concat gc2Curr)
  in  if result
      then gc2Aux (termMatchDSs termMatch curr) curr
      else filter (\(a,_) -> not a) (concat gc2Curr)

gc2DSSameClause :: DSet -> [(Bool, GCDetails)]
gc2DSSameClause ds@(DS {coTree' = ct, prg' = prog}) =
  let max = length prog
      repeatedCL = map (repeatedClause ct) [1..max]
      terms = map (getTerms ct) repeatedCL
      --termsMod = map (reformulateTerms) (zip [1..max] terms)
      checked = map (gc2PairwiseAux ds) terms
      result = and $ map (fst) (concat checked)
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat checked)

gc2Clause :: Program -> ClauseTree -> [(Bool, GCDetails)]
gc2Clause prog ct =
  let ds = [initDS {coTree' = (initGoal $ [clHead ct]), prg' = prog, clMap' = (cotsToCM prog [])}]
  in  gc2Aux ds ds


gc2Prog :: Program -> [(Bool, GCDetails)]
gc2Prog prog = 
  let gc2ed = map (gc2Clause prog) prog
      result = and $ map (fst) (concat gc2ed)
  in  if  result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat gc2ed)

gc2Items :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, GCDetails)]
gc2Items (prog, _, _) = gc2Prog prog


--------------------------------------------------------------------------------
---------------------------------------GC3--------------------------------------
--------------------------------------------------------------------------------

--gc3Checks :: ([[Int]] -> [[Int]] -> [[Int]]) -> DState ([(Maybe Bool, GCDetails)])
--gc3Checks prioF = do
--  (queue@(curr:rest),dss) <- get
--  let unified     = unifyDS unify dss
--      dTreeUN     = if unified == [] && (not $ completeCoInTree (coTree' dss)) 
--                    then (ee $ superAddToCTree dtree curr (DElemBool False))
--                    else dtree
--      incUN       = filter (incompleteDS) unified
--      compUN      = filter (completeDS) unified
--      termMatched = fullTermMatchDS incUN incUN
--      compTM      = filter (completeDS) termMatched
--      incTM       = filter (incompleteDS) termMatched
--      gc2Check    = gc2Aux incTM incTM 
--      gc2result   = and $ map (fst) gc2Check
--      toAdd       = compUN ++ compTM
--      newDTree    = addDStoDT dTreeUN curr toAdd 
--      newDomains  = if toAdd == []
--                    then [curr ++ [1]]
--                    else map (\x -> curr ++ [x]) [1..(length toAdd)]
--  if gc2result
--  then do 
--       let (result, next) = gc3TerminationCheck incTM
--           newNext = nubBy (eqDS) next
--       put $ (prioF rest newDomains, newDTree)
--       return $ ([(result,dummyGCDetails)], (map snd newNext))
--  else return $ (map (\(a,b) -> (Just a,b)) $ filter (\(a,_) -> not a) gc2Check, [])

processGC3 :: ([[Int]] -> [[Int]] -> [[Int]]) -> DState [(Maybe Bool, GCDetails)]
processGC3 prioF = do
  (queue@(curr:rest),dtree@(CTree _ _ m)) <- get
  let nextDSet = fromJust $ Map.lookup curr m
  case nextDSet of
    DElemBool v -> do 
      put $ (rest,dtree)
      return []
    DElemDS  ds -> do --
      let unified     = unifyDS unify ds
          dTreeUN     = if unified == [] && (not $ completeCoInTree (coTree' ds)) 
                        then (ee $ superAddToCTree dtree curr (DElemBool False))
                        else dtree
          incUN       = filter (incompleteDS) unified
          compUN      = filter (completeDS) unified
          gc2CheckUN  = gc2Aux incUN incUN
          gc2resultUN = and $ map (fst) gc2CheckUN
          termMatched = fullTermMatchDS incUN incUN
          incTM       = filter (incompleteDS) termMatched
          compTM      = filter (completeDS) termMatched
          gc2CheckTM  = gc2Aux incTM incTM 
          gc2resultTM = and $ map (fst) gc2CheckTM
          gc3ed       = gc3DSCheck gc3TestDS' incTM
          toAdd       = compUN ++ compTM ++ gc3ed
          newDTree    = addDStoDT dTreeUN curr toAdd 
          newDomains  = if toAdd == []
                        then [curr ++ [1]]
                        else map (\x -> curr ++ [x]) [1..(length toAdd)]
      if gc2resultUN
      then if gc2resultTM
           then do
                put $ (prioF rest newDomains, newDTree)
                return ([])
           else return $ (map (\(a,b) -> (Just a,b)) $ filter (\(a,_) -> not a) gc2CheckTM)
      else return $ (map (\(a,b) -> (Just a,b)) $ filter (\(a,_) -> not a) gc2CheckUN)

gc3 :: ([[Int]] -> [[Int]] -> [[Int]]) -> StateT (Queue,DTree) Data.Functor.Identity.Identity ([(Maybe Bool, GCDetails)])
gc3 prioF = do
  result <- processGC3 prioF
  (q,dt) <- get
  if result /= []
  then return result
  else if q == []
       then return [(Just True, dummyGCDetails)]
       else gc3 prioF

gc3N :: Int ->  ([[Int]] -> [[Int]] -> [[Int]]) -> StateT (Queue,DTree) Data.Functor.Identity.Identity ([(Maybe Bool, GCDetails)])
gc3N 0 _ = return []
gc3N n prioF = do
  result <- processGC3 prioF
  (q,dt) <- get
  if result /= []
  then return result
  else if q == []
       then return [(Just True, dummyGCDetails)]
       else gc3N (n-1) prioF 

gc3Check :: ([ClauseTree], [[TermTree]], [String]) -> (Queue,DTree) -> ([(Maybe Bool, GCDetails)], (Queue, DTree))
gc3Check items@(pr, (g:gs), cots) ([],dt)
  | dt == empty = gc3Check items (firstTime items)
  | otherwise   = ([(Just True,dummyGCDetails)], ([],dt))
gc3Check _ (q,dt) = runState (gc3 prioBreadthFirst) (q,dt)

gc3CheckDebug :: Int -> ([ClauseTree], [[TermTree]], [String]) -> (Queue,DTree) -> ([(Maybe Bool, GCDetails)], (Queue, DTree))
gc3CheckDebug n items@(pr, (g:gs), cots) ([],dt)
  | dt == empty = gc3CheckDebug n items (firstTime items)
  | otherwise   = ([(Just True,dummyGCDetails)], ([],dt))
gc3CheckDebug n _ (q,dt) = runState (gc3N n prioBreadthFirst) (q,dt)

gc3Clause :: Program -> [String] -> ClauseTree -> [(Maybe Bool, GCDetails)]
gc3Clause prog cm ct = fst $ gc3Check (prog, [[clHead ct]], cm) ([], empty)    

gc3Prog :: Program -> [String] -> [(Bool, GCDetails)]
gc3Prog prog cm = 
  let gc3ed = map (gc3Clause prog cm) prog
      result = and $ map (fromJust . fst) (concat gc3ed)
  in  if  result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) $ map (\(a,b) -> (fromJust a,b)) (concat gc3ed)

gc3Items :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, GCDetails)]
gc3Items (prog, _, cm) = gc3Prog prog cm
