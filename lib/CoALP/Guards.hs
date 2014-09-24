-- 01/08/2014
-- GC2 Working

module CoALP.Guards where

import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.CTree
import CoALP.Substitution
import CoALP.CoInTree
import CoALP.OldProcess
import CoALP.UI.Printer

import Control.Monad.State.Lazy
import Data.Functor.Identity
import Data.Maybe
import Data.List
import           Data.Map (Map)
import qualified Data.Map as Map

type GCDetails = (XSubst,WorkingSet,[TermTree])

dummyWS = WS empty [] Map.empty Map.empty 0

dummyGCDetails = (dummyXSubst, dummyWS, [])

saveGCs :: String -> [(Bool, GCDetails)] -> IO ()
saveGCs id results =
  let trees = map (coTree . snd3 . snd) results
  in  saveCoIn id 0 trees

drawGCs :: [(Bool, GCDetails)] -> IO ()
drawGCs results =
  putStrLn $ concat $ map (drawGC) results

drawGC :: (Bool, GCDetails) -> String
drawGC (result,(subs,ws,checked))
  | result = show result
  | otherwise = "\n" ++ show result ++
      "\nSubstitution: " ++ show0 subs ++
      "\nClause: " ++ clauseTreeToString clause ++
      "\nGC Checked 0: " ++ termTreeToString (checked !! 0) ++
      "\nGC Checked 1: " ++ termTreeToString (checked !! 1)
    where clause = (prg ws) !! ((fst subs) - 1)

guarded :: Program -> [String] -> (Bool, [String])
guarded prog cm
  | (fst $ head gc1Result) == False = (False, ["GC1 unguarded"] ++ (map (termTreeToString) $ (concat $ map snd gc1Result)) )
  | (fst $ head gc2Result) == False = (False, ["GC2 unguarded"] ++ (map (drawGC) gc2Result) )
  | (fst $ head gc3Result) == False = (False, ["GC3 unguarded"] ++ (map (drawGC) gc3Result) )
  | otherwise = (True, [])
  where gc1Result = gc1Prog' prog
        gc2Result = gc2Prog' prog
        gc3Result = gc3Prog' prog cm

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

gc1Items :: ([ClauseTree], [[TermTree]], [String]) -> Bool
gc1Items (prg,_,_) = gc1Prog prg

gc1Prog :: Program -> Bool
gc1Prog prg = and $ map gc1Clause prg

gc1Clause :: ClauseTree -> Bool
gc1Clause ct =
  let terms = termsWithHead ct
  in  if terms == []
      then True
      else and $ map (gc1 (clHead ct)) terms

gc1 :: TermTree -> TermTree -> Bool
gc1 t0 t1 = constantGuard t0 t1 || corecursiveReduct t0 t1

gc1Aux :: TermTree -> TermTree -> (Bool, [TermTree])
gc1Aux t0 t1 =
  if constantGuard t0 t1 || corecursiveReduct t0 t1
  then (True, [])
  else (False, (t0:t1:[]))

gc1Items' :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, [TermTree])]
gc1Items' (prg,_,_) = gc1Prog' prg

gc1Prog' :: Program -> [(Bool, [TermTree])]
gc1Prog' prg =
  let gc1ed = map gc1Clause' prg
      result = and $ map (fst) (concat gc1ed)
  in  if  result
      then [(True, [])]
      else filter (\(a,_) -> not a) (concat gc1ed)

gc1Clause' :: ClauseTree -> [(Bool, [TermTree])]
gc1Clause' ct =
  let terms = termsWithHead ct
      gc1ed = map (gc1Aux (clHead ct)) terms
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

initialWS :: ([ClauseTree], [[TermTree]], [String]) -> [WorkingSet]
initialWS (pr, (g:gs), cots) = (initWS g pr (cotsToCM pr cots))

-- Takes a  cotree and a termtree and returns all instances of that predicate in the goal tree along with their domain
repeatedPredicate :: CoInTree -> TermTree -> [([Int],TermTree)]
repeatedPredicate ct tt =
  let pred = tHead tt
      matches = Map.map (fromJust . fromTT) (Map.filter (sameTTRoot pred) (mapping ct))
  in  Map.toList matches

sameTTRoot v (TT a) = sameAsRoot v a
sameTTRoot _ _ = False

-- Takes a working set and returns the instances that the predicate appears
gc2WSRepeatPred :: WorkingSet -> [([Int],TermTree)]
gc2WSRepeatPred (WS ct prg _ _ _) =
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

gc2WSSameClause :: WorkingSet -> Maybe Bool
gc2WSSameClause (WS ct prg _ _ _) =
  let max = length prg
      repeatedCL = map (repeatedClause ct) [1..max]
      terms = map (getTerms ct) repeatedCL
  in  Just $ and $ map (gc2Pairwise) terms

getTerms :: CoInTree -> [[Int]] ->  [([Int],TermTree)]
getTerms ct@(CTree _ _ m) ds =
  let terms = map (fromJust . (flip Map.lookup m)) (map init ds)
      lastDs = lastDomains ds
      extraDs = concat $ map (flip sharedPredChild ct) lastDs
      extraTerms = map (fromJust . (flip Map.lookup m)) extraDs
  in  zip ds (map (fromJust . fromTT) terms) ++ zip extraDs (map (fromJust . fromTT) extraTerms)

gc2Pairwise :: [([Int],TermTree)] -> Bool
gc2Pairwise reps = and $ map (gc2Pairwise' reps) reps

gc2Pairwise' :: [([Int],TermTree)] -> ([Int],TermTree) -> Bool
gc2Pairwise' reps rep@(d,t) =
  let filtered = filter (\(a,b) -> d `isPrefixOf` a && d /= a) reps
  in  and $ map ((gc1 t) . snd) filtered

gc2CheckRep :: WorkingSet -> Maybe Bool
gc2CheckRep ws
  | length (gc2WSRepeatPred ws) <= 1 = Nothing
  | otherwise = Just $ gc2Pairwise (gc2WSRepeatPred ws)

gc2 :: [WorkingSet] -> [WorkingSet] -> Bool
gc2 []   _    = True
gc2 curr prev =
  let gc2Curr = map (gc2WSSameClause) curr
      filtered = catMaybes gc2Curr
  in  if and filtered == False
      then False
      else gc2 (termMatchWSs termMatch curr) curr

gc2Clause :: Program -> ClauseTree -> Bool
gc2Clause prg ct =
  let ws = [WS (initGoal $ [clHead ct]) prg Map.empty (cotsToCM prg []) 0]
  in  gc2 ws ws

gc2Prog :: Program -> Bool
gc2Prog prog = and $ map (gc2Clause prog) prog

gc2Items :: ([ClauseTree], [[TermTree]], [String]) -> Bool
gc2Items (prog, _, _) = gc2Prog prog

gc2Aux :: [WorkingSet] -> [WorkingSet] -> [(Bool, GCDetails)]
gc2Aux []   _    = [(True, dummyGCDetails)]
gc2Aux curr prev =
  let gc2Curr = map (gc2WSSameClause') curr
      result = and $ map (fst) (concat gc2Curr)
  in  if result
      then gc2Aux (termMatchWSs termMatch curr) curr
      else filter (\(a,_) -> not a) (concat gc2Curr)

gc2WSSameClause' :: WorkingSet -> [(Bool, GCDetails)]
gc2WSSameClause' ws@(WS ct prg _ _ _) =
  let max = length prg
      repeatedCL = map (repeatedClause ct) [1..max]
      terms = map (getTerms ct) repeatedCL
      --termsMod = map (reformulateTerms) (zip [1..max] terms)
      checked = map (gc2PairwiseAux ws) terms
      result = and $ map (fst) (concat checked)
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat checked)

reformulateTerms :: (Int,[([Int],TermTree)]) -> [(Int, ([Int],TermTree))]
reformulateTerms (a,b) = map (\(c,d) -> (a,(c,d))) b

gc2PairwiseAux :: WorkingSet -> [([Int],TermTree)] -> [(Bool, GCDetails)]
gc2PairwiseAux ws reps =
  let gc1pairwise = map (gc2Pairwise'' ws reps) reps
      result = and $ map (fst) (concat gc1pairwise)
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat gc1pairwise)

gc2Pairwise'' :: WorkingSet ->  [([Int],TermTree)] -> ([Int],TermTree) -> [(Bool, GCDetails)]
gc2Pairwise'' ws@(WS ct prog _ _ _) reps rep@(d,t) =
  let filtered = filter (\(a,b) -> d `isPrefixOf` a && d /= a) reps
      gc1ed = map ((gc1Aux t) . snd) filtered -- [(Bool, [TermTree])]
      result = and $ map (fst) gc1ed
      merged = zip (map fst filtered) gc1ed
      rearrage = map (\(a,(b,c)) -> (b, (fromJust $ fromXSub $ fromJust $ getCoIn a, c))) merged
      getCoIn = flip Map.lookup (mapping ct)
      replace = map (\(a, (b,c)) -> (a, ( b, ws, c))) rearrage
  in  if result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) replace

--(XSubst,ClauseTree,TermTree,[TermTree])

gc2Clause' :: Program -> ClauseTree -> [(Bool, GCDetails)]
gc2Clause' prg ct =
  let ws = [WS (initGoal $ [clHead ct]) prg Map.empty (cotsToCM prg []) 0]
  in  gc2Aux ws ws

gc2Prog' :: Program -> [(Bool, GCDetails)]
gc2Prog' prog =
  let gc2ed = map (gc2Clause' prog) prog
      result = and $ map (fst) (concat gc2ed)
  in  if  result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat gc2ed)

gc2Items' :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, GCDetails)]
gc2Items' (prog, _, _) = gc2Prog' prog

--------------------------------------------------------------------------------
---------------------------------------GC3--------------------------------------
--------------------------------------------------------------------------------


-- Processes the working set the number of times supplied returning the solutions and the last step
itGC3 :: [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity (Maybe Bool)
itGC3 mem = do
  (result, newMem) <- gc3Checks mem
  case result of
    Nothing -> itGC3 newMem
    Just _ -> return result


itGC3Debug :: Int -> [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity (Maybe Bool)
itGC3Debug n mem = do
  (result, newMem) <- gc3Checks mem
  if n == 0
  then return Nothing
  else case result of
       Nothing -> itGC3Debug (n-1) newMem
       Just _ -> return result

gc3Checks :: [Memory] -> WorkState (Maybe Bool, [Memory])
gc3Checks mem = do
  wss <- get
  let unified = unifyWSs' unify wss
      memAsigned = map (\(a,(b,c)) -> (a,b,c)) (zip mem unified)
      incUN = filterIncom memAsigned
      termMatched = fullTermMatch' incUN incUN
      incTM = filterIncom termMatched
      gc2List = concat $ map (CoALP.OldProcess.thd3) incTM
      gc2Check = gc2 gc2List gc2List
  if gc2Check
  then do
       let (result, next) = gc3TerminationCheck incTM
           newNext = nubBy (eqWS') next
       put (map fst newNext)
       return $ (result, (map snd newNext))
  else return $ (Just False, [])

eqWS' :: (WorkingSet,a) -> (WorkingSet,a) -> Bool
eqWS' ((WS gt0 _ _ _ _),_) ((WS gt1 _ _ _ _),_) = gt0 `eqCoIn` gt1

gc3TerminationCheck :: [(Memory,WorkingSet,[WorkingSet])] -> (Maybe Bool, [(WorkingSet,Memory)])
gc3TerminationCheck wss =
  let gc3ed = gc3WSCheck gc3Test wss
      filtered = filter (\(a,b) -> not $ completeCoInTree (coTree a)) gc3ed
  in if wss == [] || filtered == []
     then (Just True, [])
     else (Nothing, filtered)



getSubs :: SubstTree -> [[Int]] -> [([Int],(Int,Subst))]
getSubs (CTree _ _ m) ds =
  let subs = map (fromJust . (flip Map.lookup m)) ds
  in  zip ds subs

gc3Compare :: Program -> [([Int],(Int,Subst))] -> Bool
gc3Compare prog reps
  | length reps < 3 = False
  | otherwise = or $ map (gc3Compare' cl reps) reps
    where cl = prog !! ((fst $ snd $ head reps) - 1)

gc3Compare' :: ClauseTree -> [([Int],(Int,Subst))] -> ([Int],(Int,Subst)) -> Bool
gc3Compare' cl reps rep@(d ,(cn,sub)) =
  let filtered = filter (\(a,b) -> d `isPrefixOf` a && d /= a) reps
      result
        | length filtered < 3 = False
        | otherwise = gc3Compare'' cl (map (snd . snd) filtered)
  in  result

gc3Compare'' :: ClauseTree ->  [Subst] -> Bool
gc3Compare'' _ (_:_:[])  = False
gc3Compare'' cl (x0:x1:x2:xs) = (compareSub cl x0 x1 && compareSub cl x1 x2) || gc3Compare'' cl (x1:x2:xs)


compareSub :: ClauseTree -> Subst -> Subst -> Bool
compareSub cl s0 s1 =
  let l0 = Map.toList s0
      l1 = Map.toList s1
      jointList = zip l0 l1
  in  or $ map (\(a,b) -> compareTermTree cl (s0, a) (s1, b)) jointList


compareTermTree :: ClauseTree -> (Subst, (String, TermTree)) -> (Subst, (String, TermTree)) -> Bool
compareTermTree cl (s0 ,(str0, t0@(CTree _ d0 m0))) (s1, (str1, t1@(CTree _ d1 m1))) =
  let disTree = pairTree t0 t1
      reducedMap = Map.map reduceVar (mapping disTree)
      disMap = Map.filter (\(a,b) -> a /= b) reducedMap
  in  if disMap == Map.empty
      then True
      else checkForVarMatch cl (s0, t0) (s1, t1) disMap

checkForVarMatch :: ClauseTree -> (Subst, TermTree) -> (Subst, TermTree) -> Map [Int] (String, String) -> Bool
checkForVarMatch cl (s0, t0) (s1, t1) dm =
  let diffDoms = Map.keys dm
      diffSubTree = map (\x -> (ee $ getSubCTree t0 x, ee $ getSubCTree t1 x)) diffDoms
      eqSubTree = map (\(a,b) -> (findMatchingVar a s0, findMatchingVar b s1)) diffSubTree
      dummy = False
  in  dummy


findMatchingVar :: TermTree -> Subst -> [String]
findMatchingVar t0 sub0
  | filtered == Map.empty = []
  | otherwise = keys
    where filtered = Map.filter (eqCTreeLoose t0) sub0
          keys = Map.keys filtered


reduceVar :: (String,String) -> (String,String)
reduceVar (a,b)
  | isVariable a && isVariable b = (variablePart a, variablePart b)
  | isVariable a = (variablePart a, b)
  | isVariable b = (a, variablePart b)
  | otherwise = (a,b)


gc3Clause :: Program -> ClauseTree -> Bool
gc3Clause prog ct =
  let ws = WS (initGoal $ [clHead ct]) prog Map.empty (cotsToCM prog []) 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      (a,b) = gc3TerminationCheck inWS
      ws0 = map fst $ b
      mem = map snd $ b
  in  fromJust $ fst $ runState (itGC3 mem) ws0

gc3Prog :: Program -> Bool
gc3Prog prog = and $ map (gc3Clause prog) prog

gc3Items :: ([ClauseTree], [[TermTree]], [String]) -> Bool
gc3Items (prog, _, _) = gc3Prog prog

gc3Checks' :: [Memory] -> WorkState ([(Maybe Bool, GCDetails)] , [Memory])
gc3Checks' mem = do
  wss <- get
  let unified = unifyWSs' unify wss
      memAsigned = map (\(a,(b,c)) -> (a,b,c)) (zip mem unified)
      incUN = filterIncom memAsigned
      termMatched = fullTermMatch' incUN incUN
      incTM = filterIncom termMatched
      gc2List = concat $ map (CoALP.OldProcess.thd3) incTM
      gc2Check = gc2Aux gc2List gc2List
      gc2result = and $ map (fst) gc2Check
  if gc2result
  then do
       let (result, next) = gc3TerminationCheck incTM
           newNext = nubBy (eqWS') next
       put (map fst newNext)
       return $ ([(result,dummyGCDetails)], (map snd newNext))
  else return $ (map (\(a,b) -> (Just a,b)) $ filter (\(a,_) -> not a) gc2Check, [])

-- Processes the working set the number of times supplied returning the solutions and the last step
itGC3' :: [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity [(Maybe Bool, GCDetails)]
itGC3' mem = do
  (gc3ed, newMem) <- gc3Checks' mem
  let result
       | length gc3ed == 1 = fst (gc3ed !! 0)
       | otherwise = Just False
  case result of
    Nothing -> itGC3' newMem
    Just _ -> return gc3ed


-- Processes the working set the number of times supplied returning the solutions and the last step
itGC3'' :: Int -> [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity [(Int,(Maybe Bool, GCDetails))]
itGC3'' n mem = do
  (gc3ed, newMem) <- gc3Checks' mem
  let result
       | length gc3ed == 1 = fst (gc3ed !! 0)
       | otherwise = Just False
  case result of
    Nothing -> itGC3'' (n+1) newMem
    Just _ -> return $ zip [n..n] gc3ed

itGC3Debug' :: Int -> [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity [(Maybe Bool, GCDetails)]
itGC3Debug' n mem = do
  (gc3ed, newMem) <- gc3Checks' mem
  if n == 0
  then return gc3ed
  else let result
            | length gc3ed == 1 = fst (gc3ed !! 0)
            | otherwise = Just False
       in  case result of
             Nothing -> itGC3Debug' (n-1) newMem
             Just _ -> return gc3ed

itGC3Debug'' :: Int -> [Memory] -> StateT [WorkingSet] Data.Functor.Identity.Identity ([(Maybe Bool, GCDetails)], [Memory])
itGC3Debug'' n mem = do
  (gc3ed, newMem) <- gc3Checks' mem
  if n == 0
  then return (gc3ed, newMem)
  else let result
            | length gc3ed == 1 = fst (gc3ed !! 0)
            | otherwise = Just False
       in  case result of
             Nothing -> itGC3Debug'' (n-1) newMem
             Just _ -> return (gc3ed, newMem)

afterN :: Int -> Int -> ([ClauseTree], [[TermTree]], [String]) ->  (([(Maybe Bool, GCDetails)], [Memory]), [WorkingSet])
afterN n cn (prog, (g:gs), cots) = do
  let ws = WS (initGoal $ [clHead (prog !! (cn - 1))]) prog Map.empty (cotsToCM prog cots) 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      (a,b) = gc3TerminationCheck inWS
      ws0 = map fst $ b
      mem = map snd $ b
   in runState (itGC3Debug'' n mem) ws0

afterNDebug :: Int -> Int -> ([ClauseTree], [[TermTree]], [String]) -> [(Memory, WorkingSet)]
afterNDebug n cn items =
  let ((_,mem),wss) = afterN n cn items
  in  zip mem wss

gc3Clause' :: Program -> [String] -> ClauseTree -> [(Bool, GCDetails)]
gc3Clause' prog cm ct =
  let ws = WS (initGoal $ [clHead ct]) prog Map.empty (cotsToCM prog cm) 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      (a,b) = gc3TerminationCheck inWS
      ws0 = map fst $ b
      mem = map snd $ b
  in  map (\(a,b) -> (fromJust a, b)) $ fst $ runState (itGC3' mem) ws0

gc3Clause'' :: Program -> [String] -> ClauseTree -> [(Int, (Bool, GCDetails))]
gc3Clause'' prog cm ct =
  let ws = WS (initGoal $ [clHead ct]) prog Map.empty (cotsToCM prog cm) 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      (a,b) = gc3TerminationCheck inWS
      ws0 = map fst $ b
      mem = map snd $ b
  in  map (\(n,(a,b)) -> (n,(fromJust a, b))) $ fst $ runState (itGC3'' 0 mem) ws0

gc3Prog' :: Program -> [String] -> [(Bool, GCDetails)]
gc3Prog' prog cm =
  let gc3ed = map (gc3Clause' prog cm) prog
      result = and $ map (fst) (concat gc3ed)
  in  if  result
      then [(True, dummyGCDetails)]
      else filter (\(a,_) -> not a) (concat gc3ed)

gc3Items' :: ([ClauseTree], [[TermTree]], [String]) -> [(Bool, GCDetails)]
gc3Items' (prog, _, cm) = gc3Prog' prog cm

saveAfter :: String -> Int -> Int -> ([ClauseTree], [[TermTree]], [String]) ->  IO ()
saveAfter s n cn (prog, (g:gs), cots) = do
  let ws = WS (initGoal $ [clHead (prog !! (cn - 1))]) prog Map.empty (cotsToCM prog cots) 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      (a,b) = gc3TerminationCheck inWS
      ws0 = map fst $ b
      mem = map snd $ b
      after = runState (itGC3Debug' n mem) ws0
  saveCoIn' (s ++ "-" ++ show n ++ "-after") 0 (map coTree (snd after))
