-- 18/08/2014
-- CoTree Processing

module CoALP.OldProcess where

import CoALP.CTree	
import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.CoInTree
import CoALP.Substitution
import CoALP.UI.Parser
import CoALP.UI.Dot
--import CoALP.Guards (gc3WSCheck)

import Data.List
import Data.Maybe
import Data.Functor.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Control.Monad.State.Lazy

data WorkingSet = WS { coTree :: CoInTree, prg :: Program, varMap :: VarMap, clMap :: ClauseMap, varCount :: Int } deriving (Show, Eq)

type Solution = CoInTree
type WorkState = State [WorkingSet]
type ClauseMap = Map Int String
type VarMap = Map.Map String Int


type Memory = [([Int],Reduct)]

dummyReduct :: ([Int],Reduct)
dummyReduct = ([-1],(-1,[([], empty)]))

--------------------------------------------------------------------------------
---------------------------------Save Operations--------------------------------
--------------------------------------------------------------------------------

saveNCoInTree :: String -> Int -> ([ClauseTree], [[TermTree]], [String]) -> IO ()
saveNCoInTree pre n (pr, (g:gs), cots) = do
  let ((sols,wss),final) = performNSteps g pr (cotsToCM pr cots) n
      coInWSS = map (map coTree) wss
  saveCoIn (pre ++ "-CoIn-Sols") 0 sols
  saveCoInS (pre ++ "-CoIn-WS") 0 coInWSS

saveNCoInTree' :: String -> Int -> ([ClauseTree], [[TermTree]], [String]) -> IO ()
saveNCoInTree' pre n (pr, (g:gs), cots) = do
  let ((sols,wss),final) = performNSteps g pr (cotsToCM pr cots) n
      coInWSS = map (map coTree) wss
  saveCoIn' (pre ++ "-CoIn-Sols") 0 sols
  saveCoInS' (pre ++ "-CoIn-WS") 0 coInWSS

saveParentChild :: String -> Int -> ([ClauseTree], [[TermTree]], [String]) ->  IO ()
saveParentChild pre n (pr, (g:gs), cots) = do
  let (wss, _) = performNStepsDebug g pr (cotsToCM pr cots) n
  saveParCh' pre 0 wss


saveParCh' :: String -> Int -> [[(Memory,WorkingSet,[WorkingSet])]] -> IO ()
saveParCh' _ _ [] = return ()
saveParCh' s n (set0:sets) = do
  let memRemoved = map (\(a,b,c) -> (b,c)) set0
  saveParCh (s ++ "-" ++ show n ++ "-it" ) 0 memRemoved
  saveParCh' s (n+1) sets

saveParCh :: String -> Int -> [(WorkingSet,[WorkingSet])] -> IO ()
saveParCh _ _ [] = return ()
saveParCh s n ((wsP,wsC):wss) = do
  let parent = coTree wsP
      children = map coTree wsC
  saveCoIn' (s ++ "-" ++ show n ++ "-P" ) 0 [parent]
  saveCoIn' (s ++ "-" ++ show n ++ "-C" ) 0 children
  saveParCh s (n+1) wss
  
performNStepsDebug :: Goal -> Program -> ClauseMap -> Int -> ([[(Memory,WorkingSet,[WorkingSet])]], [WorkingSet])
performNStepsDebug g pr cm n = 
  let (initialWS, initMem) = initWS' g pr cm
  in  runState (itProcessDebug n initMem []) initialWS
--------------------------------------------------------------------------------
-------------------------------Process Operations-------------------------------
--------------------------------------------------------------------------------

-- Find first solution
findFirstSolution :: ([ClauseTree], [[TermTree]], [String]) -> ([Solution], [WorkingSet])
findFirstSolution (pr, (g:gs), cots) = 
  let ws = WS (initGoal g) pr Map.empty (cotsToCM pr cots) 0
      --dummyMem =  [(replicate (length ws) dummyReduct)]
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      gc3ed = gc3WSCheck gc3Test' inWS
      ws0 = map fst $ gc3ed
      mem = map snd $ gc3ed
  in  runState (firstSolution mem []) ws0

firstSolution :: [Memory] -> [Solution] -> StateT [WorkingSet] Data.Functor.Identity.Identity [Solution]
firstSolution mem [] = do
  (newSols, newMem) <- processState mem
  wss <- get
  if wss == []
  then return newSols
  else firstSolution newMem newSols
firstSolution _ sol = return sol

findNextSolution :: ([ClauseTree], [[TermTree]], [String]) -> [WorkingSet] -> [Memory] -> (([Solution],[Memory]), [WorkingSet])
findNextSolution items@(pr, (g:gs), cots) [] [] =
  let ws = WS (initGoal g) pr Map.empty (cotsToCM pr cots) 0
      --dummyMem =  [(replicate (length ws) dummyReduct)]
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      gc3ed = gc3WSCheck gc3Test' inWS
      ws0 = map fst $ gc3ed
      mem = map snd $ gc3ed
  in  findNextSolution items ws0 mem
findNextSolution _ []  _   = (([],[]),[])
findNextSolution _ wss mem = runState (nextSolution mem []) wss
 
nextSolution :: [Memory] -> [Solution] -> StateT [WorkingSet] Data.Functor.Identity.Identity ([Solution],[Memory])
nextSolution mem [] = do
  (newSols, newMem) <- processState mem
  wss <- get
  if wss == []
  then return (newSols,[])
  else nextSolution newMem newSols
nextSolution mem sol = return (sol,mem)


-- TODO make work with multiple seperate goals
performN :: Int -> ([ClauseTree], [[TermTree]], [String]) -> ([Solution], [WorkingSet])
performN n (pr, (g:gs), cots) = getNthStep g pr (cotsToCM pr cots) n

-- Gets the Nth step and returns it and all the solutions found
getNthStep :: Goal -> Program -> ClauseMap -> Int -> ([Solution], [WorkingSet])
getNthStep g pr cm n = 
  let (initialWS, initMem) = initWS' g pr cm
  in  runState (itProcess n initMem []) initialWS

--debugN  :: Int -> ([ClauseTree], [[TermTree]], [String]) -> ([(Memory,WorkingSet,[WorkingSet])], [WorkingSet])
--debugN n (pr, (g:gs), cots) = debugNthStep g pr (cotsToCM pr cots) n

--debugNthStep :: Goal -> Program -> ClauseMap -> Int -> ([(Memory,WorkingSet,[WorkingSet])], [WorkingSet])
--debugNthStep g pr cm n =
--  let (initialWS, initMem) = initWS' g pr cm
--  in  runState (itProcessDebug n initMem [] ) initialWS

-- Performs N steps and returns all solutions and each step
performNSteps :: Goal -> Program -> ClauseMap -> Int -> (([Solution],[[WorkingSet]]), [WorkingSet])
performNSteps g pr cm n = 
  let (initialWS, initMem) = initWS' g pr cm
  in  runState (itProcess' n initMem ([],[initialWS])) initialWS

-- Processes the working set the number of times supplied returning the solutions and the last step
itProcess :: Int -> [Memory] -> [Solution] -> StateT [WorkingSet] Data.Functor.Identity.Identity [Solution]
itProcess 0 _ sols = return sols
itProcess i mem sols = do
  (newSols, newMem) <- processState mem
  itProcess (i-1) newMem (sols ++ newSols)

-- Processes the working set the number of times supplied returning the solutions and all steps
itProcess' :: Int -> [Memory] -> ([Solution], [[WorkingSet]]) -> StateT [WorkingSet] Data.Functor.Identity.Identity ([Solution],[[WorkingSet]])
itProcess' 0 _ ans = return ans
itProcess' i mem (sols,wss) = do
  (newSols, newMem) <- processState mem
  newWS   <- get
  itProcess' (i-1) newMem ((sols ++ newSols), (wss ++ [newWS]))

-- Processes the working set the number of times supplied returning the solutions and the last step
itProcessDebug :: Int -> [Memory] -> [[(Memory,WorkingSet,[WorkingSet])]]  -> StateT [WorkingSet] Data.Functor.Identity.Identity [[(Memory,WorkingSet,[WorkingSet])]]
itProcessDebug 0 _   results = return results
itProcessDebug i mem results = do
  (parChild, newMem) <- processStateDebug mem
  itProcessDebug (i-1) newMem (results ++ [parChild])


--Processes a working state
processState :: [Memory] -> WorkState ([Solution], [Memory])
processState mem = do
  wss <- get
  let unified = unifyWSs' unify wss
      memAsigned = map (\(a,(b,c)) -> (a,b,c)) (zip mem unified)
      incUN = filterIncom memAsigned
      compUM = filterCom memAsigned
      termMatched = fullTermMatch' incUN incUN
      incTM = filterIncom termMatched
      compTM = filterCom termMatched
      gc3ed = gc3WSCheck gc3Test' incTM
      inc = filter (\(a,b) -> not $ completeCoInTree (coTree a)) gc3ed
      comp = map fst $ filter (\(a,b) -> completeCoInTree (coTree a)) gc3ed
      solutions = map (coTree) (compUM ++ compTM ++ comp)
  put $ map fst inc
  return (solutions, (map snd inc))

processStateDebug :: [Memory] -> WorkState ([(Memory,WorkingSet,[WorkingSet])], [Memory])
processStateDebug mem = do
  wss <- get
  let unified = unifyWSs' unify wss
      memAsigned = map (\(a,(b,c)) -> (a,b,c)) (zip mem unified)
      incUN = filterIncom memAsigned
      compUM = filterCom memAsigned
      termMatched = fullTermMatch' incUN incUN
      incTM = filterIncom termMatched
      compTM = filterCom termMatched
      gc3ed = gc3WSCheck gc3Test' incTM
      inc = filter (\(a,b) -> not $ completeCoInTree (coTree a)) gc3ed
      comp = map fst $ filter (\(a,b) -> completeCoInTree (coTree a)) gc3ed
      solutions = map (coTree) (compUM ++ compTM ++ comp)
  put $ map fst inc
  return (incTM,(map snd inc))


filterIncom :: [(Memory, WorkingSet,[WorkingSet])] -> [(Memory, WorkingSet,[WorkingSet])]
filterIncom wss = 
  let preFiltered = map (\(m,a,b) -> (m,a, filter (incompleteWS) b)) wss
      filtered = filter (\(m,a,b) -> b /= []) preFiltered
  in  filtered


filterCom :: [(Memory, WorkingSet,[WorkingSet])] -> [WorkingSet]
filterCom wss = 
  let filtered = map (\(m,a,b) -> filter (completeWS) b) wss
  in  concat $ filtered


-- Fully matches terms in a working set until no more matches can be made
fullTermMatch' :: [(Memory, WorkingSet,[WorkingSet])] -> [(Memory, WorkingSet,[WorkingSet])] ->  [(Memory, WorkingSet,[WorkingSet])]
fullTermMatch' []         prev = prev
fullTermMatch' curr       prev 
  | curr == prev = prev
  | otherwise    = fullTermMatch' next curr
    where next = map (\(m,a,b) -> (m,a, concat $ map snd (termMatchWSs' termMatch b))) curr
  
termMatchWSs' :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
         [WorkingSet] -> [(WorkingSet,[WorkingSet])]
termMatchWSs' f ws = map (\x -> (x, termMatchWS f x)) ws

unifyWSs' :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
         [WorkingSet] -> [(WorkingSet,[WorkingSet])]
unifyWSs' f ws = map (\x -> (x, unifyWS f x)) ws

--------------------------------------------------------------------------------
-----------------------------Working Set Operations-----------------------------
--------------------------------------------------------------------------------

-- Makes a clause map from a program (by default makes all terms inductive)
makeCM :: Program -> ClauseMap
makeCM pr = foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip [1..(length pr)] (repeat "i"))

-- Converts a list of coinductive terms into a clause map
cotsToCM :: Program -> [String] -> ClauseMap
cotsToCM pr strs = 
  let cots = concat $ map (cotsNum pr) strs
      cotsMap = foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip cots (repeat "c"))
  in  Map.union cotsMap (makeCM pr)

-- gets the number of the coinductive clauses
cotsNum :: Program -> String -> [Int]
cotsNum pr s = map fst $ filter (cotsCL s) (enumProg pr)

-- Check if the string matches the head of the clause
cotsCL :: String -> (Int, ClauseTree) ->  Bool
cotsCL s (_,ct) = (tHead $ clHead ct) == s

eqWS :: WorkingSet -> WorkingSet -> Bool
eqWS (WS ct0 _ _ _ _) (WS ct1 _ _ _ _ ) = ct0 `eqCoIn` ct1

-- Initialise a goal as a list of working sets
initWS :: Goal -> Program -> ClauseMap -> [WorkingSet]
initWS g pr cm = 
--  let ws = [WS (initGoal g) (mergeProg pr) Map.empty cm []]
  let ws = [WS (initGoal g) pr Map.empty cm 0]
  in  fullTermMatch ws ws

initWS' :: Goal -> Program -> ClauseMap -> ([WorkingSet],[Memory])
initWS' g pr cm =
  let ws = WS (initGoal g) pr Map.empty cm 0
      inWS = fullTermMatch' [([dummyReduct],ws,[ws])] [([dummyReduct],ws,[ws])]
      gc3ed = gc3WSCheck gc3Test' inWS
      ws0 = map fst $ gc3ed
      mem = map snd $ gc3ed
  in  (ws0, mem)

initGoal :: Goal -> CoInTree
initGoal g =
  let goalList = map (convertToFnString [[]]) g
      stringGoal = "endGoal: " ++ (concat $ (map (++ ",") (init goalList))) ++ last goalList
  in  makeCoInTree ([makeTermTree (Map.insert [] stringGoal  Map.empty)] ++ g)

-- Converts between paired format to a working set
--makeWS :: CoInTree -> ClauseMap -> (Program, VarMap) -> WorkingSet
--makeWS ct cm (pr, vm) = WS ct pr vm cm

makeWS' :: (Program, VarMap) -> ClauseMap -> [(Int,CoInTree)] -> [WorkingSet]
makeWS' (pr,vm) cm cts = map (makeHelper pr vm cm) cts

makeHelper :: Program -> VarMap -> ClauseMap -> (Int,CoInTree) -> WorkingSet
makeHelper pr vm cm (vc,ct) = WS ct pr vm cm vc

--------------------------------------------------------------------------------
----------------------------------Term match------------------------------------
--------------------------------------------------------------------------------

-- Fully matches terms in a working set until no more matches can be made
fullTermMatch :: [WorkingSet] -> [WorkingSet] ->  [WorkingSet]
fullTermMatch []   prev = prev
fullTermMatch curr prev = fullTermMatch (termMatchWSs termMatch curr) curr

-- Processes a list of working sets and returns the next list of working sets
termMatchWSs :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
         [WorkingSet] -> [WorkingSet]
termMatchWSs f ws = nubBy (eqWS) $ concat $ map (termMatchWS f) ws

-- For term matching
termMatchWS :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->	
         WorkingSet -> [WorkingSet]
termMatchWS f (WS ct pr vm cm vc) = 
  let gls = filter (leafFilter) (zip (findLeaves ct) (findLeavesValue ct))
      domains = map (fst) gls
      leaves = coInElemToTT $ map (snd) gls
      program = runState (renameProgWithCT pr ct) vm
      idxPrg = (enumProg (fst program))
      substs = map (findClauseSubst f idxPrg) leaves
      newCoTs = map (applyTermMatch idxPrg ct vc) (zip domains substs)
  in  concat $ map (makeWS' program cm) newCoTs

-- Apply the substitutions to a CoTree
applyTermMatch :: [(Int, ClauseTree)] -> CoInTree ->  Int -> ([Int], [(Int, Subst)]) -> [(Int, CoInTree)]
applyTermMatch _ _ _ (_,[]) = []
applyTermMatch prog t vc (d,(sub@(i, _):subs)) = 
  let (nvc, substAdded) = addSubst (vc, t) (length prog) d sub
      terms = getChildren (substClause prog sub) [] 1
      termAdded = addTerms substAdded terms (d ++ [i]) 
  in  [(nvc, cleanRankAlpha $ termAdded)] ++ applyTermMatch prog t vc (d,subs)

--------------------------------------------------------------------------------
----------------------------------Unification-----------------------------------
--------------------------------------------------------------------------------

-- Processes a list of working sets and returns the next list of working sets
unifyWSs :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
         [WorkingSet] -> [WorkingSet]
unifyWSs f ws = nubBy (eqWS) $ concat $ map (unifyWS f) ws

-- Processes a single working set
unifyWS :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->	
         WorkingSet -> [WorkingSet]
unifyWS f (WS ct pr vm cm vc) = 
  let gls = filter (leafFilter) (zip (findLeaves ct) (findLeavesValue ct))
      domains = map (fst) gls
      leaves = coInElemToTT $ map (snd) gls
      program = runState (renameProgWithCT pr ct) vm
      idxPrg = (enumProg (fst program))
      substs = map (findClauseSubst f idxPrg ) leaves
      prioritized = prioritiseInductive cm (zip domains substs)
      newCoTs = map (applyUnify idxPrg ct vc) prioritized
  in  concat $ map (makeWS' program cm) newCoTs

-- Apply the substitutions to a goal tree
applyUnify :: [(Int, ClauseTree)] -> CoInTree ->  Int -> ([Int], [(Int, Subst)]) -> [(Int, CoInTree)]
applyUnify _ _ _ (_,[]) = []
applyUnify prog t vc (d,(sub:subs)) = 
  let nt = substCoInTree d prog t sub
      (nvc, substAdded) = addSubst (vc, nt) (length prog) d sub
      terms = getChildren (substClause prog sub) [] 1
      termAdded = addTerms substAdded terms (d ++ [(fst sub)]) 
  in  [(nvc, cleanRankAlpha $ termAdded)] ++ applyUnify prog t vc (d,subs)

-- Prioritises inductive substitutions by removing coinductive ones if there are any inductive subs available
prioritiseInductive :: ClauseMap -> [([Int],[(Int, Subst)])] -> [([Int],[(Int, Subst)])]
prioritiseInductive cm substs =
  let clauseNums = map (fst) $ concat $ map (snd) substs
  in  if (oneInductive cm clauseNums)
      then catMaybes $ filter (isJust) $ map (filterCoInductive cm) substs
      else substs

-- Filters any coinductive terms
filterCoInductive :: ClauseMap -> ([Int],[(Int, Subst)]) -> Maybe ([Int],[(Int,Subst)])
filterCoInductive cm (dom,subs) = 
  let inductive = filter (inductiveOnly cm) subs
  in  if length inductive == 0
      then Nothing
      else Just (dom, inductive)

-- Checks if a term is inductive
inductiveOnly :: ClauseMap  -> (Int,Subst) -> Bool
inductiveOnly cm (i,_) =
  if (Map.lookup i cm) == Just "i"
  then True
  else False

-- Checks if there is at least one inductive substitution
oneInductive :: ClauseMap -> [Int] -> Bool
oneInductive _  []     = False
oneInductive cm (x:xs) = 
  if (Map.lookup x cm) == Just "i"
  then True
  else oneInductive cm xs

--------------------------------------------------------------------------------
----------------------------Substitution Operations-----------------------------
--------------------------------------------------------------------------------

-- Substitutes in a clause
substClause :: [(Int, ClauseTree)] -> (Int, Subst) -> ClauseTree
substClause pr (i, sm) = 
  let clause = snd (pr !! (i-1))
  in  fmap''' (flip substitute sm) clause

--substGoalTree :: CTree TermTree -> (Int, Subst) -> CTree TermTree
--substGoalTree gt (_, sm) = fmap''' (flip substitute sm) gt

substCoInTree :: [Int] -> [(Int, ClauseTree)] -> CoInTree -> (Int, Subst) -> CoInTree
substCoInTree d pr ct (i, sm) = 
  let replacement = TT $ clHead $ substClause pr (i, sm)
  in  fmap''' (flip substitute' sm) $ replaceNode replacement d ct
       
--fmap''' (flip substitute' sm) ct

substitute' :: CoInElem -> Subst -> CoInElem
substitute' (TT t) sm = TT (substitute t sm)
substitute' x _ = x

-- Takes a function which finds the substitutions for term trees an enumerated program and a term tree
-- and returns a list of clause numbers and substitutions
findClauseSubst :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
          [(Int, ClauseTree)] -> TermTree -> [(Int, Subst)]
findClauseSubst f prog t =
  let substs = findSubst f t prog
      filtSubsts = filterSubst substs
  in  zip (map (fst) filtSubsts) (map (fst . snd) filtSubsts)

-- Filter all the failed attempts
filterSubst :: [(Int, Either String (Subst, TermTree))] -> [(Int, (Subst, TermTree))]
filterSubst subs = 
  let filtered = filter (validSubst) subs
      validSubst (_, Right _) = True
      validSubst (_, Left _) = False
      extract (n, Right s) = (n,s)
      extract (_, Left s) = error s
  in  map (extract) filtered

-- Given a term find the clauses which can be unified and return list of numbered clause + substitution
findSubst :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
             TermTree -> [(Int, ClauseTree)] ->  [(Int, Either String (Subst, TermTree))]
findSubst f t pr =
  let heads = map (\(k, v) -> (k, clHead v)) pr
      substs = map (\(k, v) -> (k, perform v)) heads
      perform v = 
        case f v t of
          Right (s,t) -> Right (s,t)
          Left e -> Left e
  in substs

--------------------------------------------------------------------------------
------------------------------Renaming Operations-------------------------------
--------------------------------------------------------------------------------

type ProcessSt = State VarMap

initProcessSt = Map.empty

runRenameSim :: TermTree -> [String] -> VarMap -> (TermTree, VarMap)
runRenameSim t ss vm = runState (renameTerm t ss) vm


renameGoal :: TermTree ->  ProcessSt TermTree
renameGoal tt = do
  vm <- get
  let variables = nub $ varsTerm tt
      renamed = runState (renameTerm tt variables) vm
      newMap = Map.union vm (snd renamed)
      newTerm = fst renamed
  put newMap
  return newTerm

-- Renames variables in program which match those in the CoInTree
renameProgWithCT :: Program -> CoInTree -> ProcessSt Program
renameProgWithCT pr ct = do
  vm <- get
  let variables = nub $ varsCoIn ct
      renamed = map (renameProgHelper vm variables) pr
      newMap = foldr Map.union vm (map (snd) renamed)
      newProg = map (fst) renamed
  put newMap
  return newProg

-- rearrages variables for runState so for mapping over
renameProgHelper vm ss t = runState (renameClause t ss) vm

--renameTermHelper vm ss t = runState (renameTerm t ss) vm

-- Rename variables in a Clause tree
renameClause :: ClauseTree -> [String] -> ProcessSt ClauseTree
renameClause ct [] =  return ct
renameClause ct (s:ss) = do
  m <- get
  let verboseRename = fmap'' (rnVar (variablePart s) m) ct
      newTree = fmap (snd) verboseRename
      newMap = Foldable.foldr Map.union Map.empty (fmap (fst) verboseRename)
  put newMap
  renameClause newTree ss

-- Rename variables in a Term tree
renameTerm :: TermTree -> [String] -> ProcessSt TermTree
renameTerm t [] = return t
renameTerm t (s:ss) = do
  m <- get
  (newMap, newTree) <- return (rnVar (variablePart s) m t)
  put newMap
  renameTerm newTree ss

-- Rename variable
rnVar :: String -> VarMap -> TermTree -> (VarMap, TermTree)
rnVar s1 vm t=
  let newNum = nextVar vm s1
      newMap = 
        case newNum of
          1 -> Map.insert s1 1 vm 
          otherwise -> Map.adjust (+1) s1 vm
  in  (newMap, fmap'' (rnString s1 (s1 ++ "_" ++ show newNum)) t)

-- Looks up the next variable from the map
nextVar :: VarMap -> String -> Int
nextVar m k = 
  let nxt = (Map.lookup k m)
  in case nxt of
       Nothing -> 1
       Just a -> a + 1

-- Rename String
rnString :: String -> String -> String -> String
rnString s1 s2 s0 = 
  if (variablePart s0) == s1
  then s2
  else s0 

-- get the variable part of the string (before the first _)
variablePart :: String -> String
variablePart = takeWhile (/= '_')

--------------------------------------------------------------------------------
--------------------------------GC3 Termination---------------------------------
--------------------------------------------------------------------------------

-- Performs GC3 across a set of parents and children
gc3WSCheck :: (Memory -> WorkingSet -> WorkingSet -> (WorkingSet, Memory)) -> [(Memory, WorkingSet,[WorkingSet])] -> [(WorkingSet, Memory)]
gc3WSCheck gc3Func wss =
  let-- memAssigned = map (\(a,(b,c)) -> (a,b,c)) (zip mem wss) 
      gc3ed = map (gc3Helper gc3Func) wss
  in  concat gc3ed

gc3Helper :: (Memory -> WorkingSet -> WorkingSet -> (WorkingSet, Memory)) -> (Memory, WorkingSet, [WorkingSet]) ->  [(WorkingSet, Memory)]
gc3Helper gc3Func (mem, parent, children) = (map (gc3Func mem parent) children)

gc3Test :: Memory -> WorkingSet -> WorkingSet -> (WorkingSet, Memory)
gc3Test mem parent child@(WS ct prog vm cm vc) =
  let reducts = gc3reduct' parent child
      --newTrees = map (checkReduct (coTree child) mem) reducts
      (nct, newMem) = checkReduct ct mem reducts
  in  ((WS nct prog vm cm vc), newMem)    

checkReduct :: CoInTree -> Memory -> [([Int],Reduct)] -> (CoInTree,Memory)
checkReduct ct mem [] = (ct, mem)
checkReduct ct mem ((d,reduct):reducts) =
  let matches = filter (\(a,b) ->  init a /= init d && b == reduct && snd b /= []) mem
      --parentD = init d
      --childrenD = sharedPredChild d ct
  in if matches /= []
     then checkReduct (boxBranches' ct [d]) mem reducts
     else checkReduct ct (mem ++ [(d,reduct)]) reducts

gc3Test' :: Memory -> WorkingSet -> WorkingSet -> (WorkingSet, Memory)
gc3Test' mem parent child@(WS ct prog vm cm vc) =
  let reducts = gc3reduct' parent child
      --newTrees = map (checkReduct (coTree child) mem) reducts
      (nct, newMem) = checkReduct' ct cm mem reducts
  in  ((WS nct prog vm cm vc), newMem) 

checkReduct' :: CoInTree -> ClauseMap -> Memory -> [([Int],Reduct)] -> (CoInTree,Memory)
checkReduct' ct cm mem [] = (ct, mem)
checkReduct' ct cm mem ((d,reduct):reducts) =
  let matches = filter (\(a,b) ->  init a /= init d && b == reduct && snd b /= []) mem
      --parentD = init d
      --childrenD = sharedPredChild d ct
  in if matches /= [] && Map.lookup (fst reduct) cm == Just "c"
     then --checkReduct' (boxBranches' (ct) [d]) cm mem reducts
          checkReduct' (boxBranches (addReduct ct [d] [reduct]) [d]) cm mem reducts
          --checkReduct' (boxBranches' ct [d]) cm mem reducts
     else checkReduct' ct cm (mem ++ [(d,reduct)]) reducts

sharedPredChild :: [Int] -> CoInTree ->  [[Int]]
sharedPredChild d ct =
  let children = findChildren d (mapping ct)
  in  filter (\x -> comparePred x ct) children

comparePred :: [Int] -> CoInTree -> Bool
comparePred d ct = 
  let  childPred =  tHead $ fromJust $ fromTT $ fromJust $ Map.lookup d (mapping ct)
       parentPred = tHead $ fromJust $ fromTT $ fromJust $ Map.lookup (init $ init d) (mapping ct)
  in   childPred ==  parentPred

addReduct :: CoInTree -> [[Int]] -> [Reduct] -> CoInTree
addReduct ct []     _      = ct
addReduct ct (d:ds) (r:rs) = addReduct (ee $ removeAndReplace ct d (Rdt r)) ds rs


boxBranches :: CoInTree -> [[Int]] -> CoInTree
boxBranches ct [] = ct
boxBranches ct (d:ds) = boxBranches (ee $ superAddToCTree ct d (TT trueTT)) ds

boxBranches' :: CoInTree -> [[Int]] -> CoInTree
boxBranches' ct [] = ct
boxBranches' ct (d:ds) = ee $ removeAndReplace ct d (TT trueTT)
  --let cutTree = removeFromTree ct d
  --in  boxBranches (ee $ superAddToCTree cutTree d (TT trueTT)) ds


-- FIXME not performing reducts on the correct things.

gc3reduct :: WorkingSet -> WorkingSet -> [([Int],Reduct)]
gc3reduct ws0 ws1 =
  let ct0 = coTree ws0
      ct1 = coTree ws1
      prog = map (reduceVars) (prg ws1)
      domainDiff = (domain ct1) \\ (domain ct0)
      --subMap = mapping $ substitutions ws1
      difference = map (fromJust . flip Map.lookup (mapping ct1)) domainDiff
      subs = map (subsHelper) $ filter (\(_,b) -> isCoInXSub b) (zip domainDiff difference)
      ctChildren = concat $ map (childrenHelper ct1) subs
      reducts = map (\(d,(cn ,tt)) -> (d,(cn, getReduct (clHead $ prog !! (cn - 1)) tt)) ) ctChildren
  in  nub $ reducts

gc3reduct' :: WorkingSet -> WorkingSet -> [([Int],Reduct)]
gc3reduct' ws0 ws1 =
  let parent = coTree ws0
      child = coTree ws1
      prog = map (reduceVars) (prg ws1)
      domainDiff = (domain child) \\ (domain parent)
      --subMap = mapping $ substitutions ws1
      difference = map (fromJust . flip Map.lookup (mapping child)) domainDiff
      subs = map (subsHelper) $ filter (\(_,b) -> isCoInXSub b) (zip domainDiff difference)
      clauseProjection = catCP $ map (\(newNodeD,sub) -> (newNodeD,getClauseProjection prog parent (init newNodeD) (fst sub)) ) subs
      -- getClauseProjection :: Program -> CoInTree -> [Int] -> Int -> Maybe Reduct
      -- cp :: ([Int], (Int, [([Int], TermTree)]) )
      loops = catLoops $ map (\(newNodeD,(clauseNum,reduct)) -> (newNodeD,(clauseNum,reduct),checkIfLoop child (init newNodeD) clauseNum)) clauseProjection
      coRecursiveReduct = map (\(newNodeD,xreduct,loopNode) -> (newNodeD,xreduct,loopNode,getCoRecurReduct child loopNode newNodeD) ) loops
      chreducts = map (\(newNodeD,xreduct,loopNode,coRecReducts) -> (newNodeD, checkForReductMatch xreduct coRecReducts) ) coRecursiveReduct
      -- checkIfLoop :: CoInTree -> [Int] -> Int -> Maybe [Int]
      ctChildren = concat $ map (childrenHelper child) subs
      -- getCoRecursiveReduct :: CoInTree -> [Int] -> [Int] -> Maybe [([Int],TermTree)]
      reducts = map (\(d,(cn ,tt)) -> (d,(cn, getReduct (clHead $ prog !! (cn - 1)) tt)) ) ctChildren
  in  chreducts


catCP :: [(a,Maybe b)] -> [(a,b)]
catCP vals = [(a,b) | (a,Just b) <- vals]

catLoops :: [(a,b,Maybe c)] -> [(a,b,c)]
catLoops vals =  [(a,b,c) | (a,b,Just c) <- vals]
 
--type Reduct = (Int,[([Int], TermTree)])
-- clause number, domain in clause head term tree, reduct
-- checkForReductMatch xreduct coRecReducts

checkForReductMatch :: Reduct -> [([Int],TermTree)] -> Reduct
checkForReductMatch (cn, (reducts)) (coReducts) =
  let matched = filter (flip compareReduct coReducts) reducts
  in  (cn, matched)
  

compareReduct :: ([Int],TermTree) -> [([Int],TermTree)] -> Bool
compareReduct _        [] = False
compareReduct r0@(d0,tt0) ((d1,tt1):rs)
  -- | d0 /= d1 = compareReduct r0 rs 
  | otherwise = case termMatch' tt0 tt1 of
                  Left _ -> compareReduct r0 rs
                  Right _ -> True 

getClauseProjection :: Program -> CoInTree -> [Int] -> Int -> Maybe Reduct
getClauseProjection pr ct d cn =
  let clauseTerm = clHead $ pr !! (cn -1)
      treeTerm = fromJust $ fromTT $ fromJust $ Map.lookup d (mapping ct)
      reduct = getReduct clauseTerm treeTerm
  in  if reduct /= []
      then Just (cn, reduct)
      else Nothing


-- getCoRecurReduct child loopNode newNodeD

getCoRecurReduct :: CoInTree -> [Int] -> [Int] -> [([Int],TermTree)]
getCoRecurReduct ct d0 d1 = 
  --case getCoRecursiveReduct ct d0 d1 of
  --  Just a -> a
  --  Nothing -> []
  let children = findChildren d1 (mapping ct)
      parentsChild = head $ filter (flip isPrefixOf d1) $ findChildren d0 (mapping ct)
  in  concat $ catMaybes $ map (getCoRecursiveReduct ct parentsChild) children

getCoRecursiveReduct :: CoInTree -> [Int] -> [Int] -> Maybe [([Int],TermTree)]
getCoRecursiveReduct ct d0 d1 =
  let t0 = fromJust $ fromTT $ fromJust $ Map.lookup d0 (mapping ct)
      t1 = fromJust $ fromTT $ fromJust $ Map.lookup d1 (mapping ct)
      reduct = getReduct t0 t1
  in  if reduct /= []
      then Just reduct
      else Nothing

checkIfLoop :: CoInTree -> [Int] -> Int -> Maybe [Int]
checkIfLoop _  [] _ = Nothing
checkIfLoop ct d cn 
  | isCoInXSub current && num == cn = Just d 
  | otherwise = checkIfLoop ct (init d) cn
    where current = fromJust $ Map.lookup d (mapping ct)
          (num,_) = fromJust $ fromXSub current

      
-- \(a,b) -> (a,fromJust . fromXSub b)
subsHelper :: ([Int], CoInElem) -> ([Int], XSubst)
subsHelper (a,b) = (a,fromJust $ fromXSub b)  

parentHelper :: CoInTree -> CoInTree -> ([Int], XSubst) -> ([Int],(Int, TermTree, TermTree))
parentHelper ct0 ct1 (d, (cn, _)) = 
  let tt0 = fromJust $ fromTT $ fromJust $ Map.lookup (init d) (mapping ct0)
      tt1 = fromJust $ fromTT $ fromJust $ Map.lookup (init d) (mapping ct1)
  in  (d,(cn, tt0, tt1))

childrenHelper :: CoInTree -> ([Int], XSubst) -> [([Int], (Int, TermTree))]
childrenHelper ct (d, (cn, _)) =
  let childrenD = findChildren d (mapping ct)
      children =  map (\x -> (x, Map.lookup x (mapping ct)) ) childrenD
  in  map (\(a,x) -> (a, (cn, fromJust $ fromTT $ fromJust x)) ) children

--type Reduct = (Int,[([Int], TermTree)])

reduceVars :: ClauseTree -> ClauseTree
reduceVars ct = fmap'' (fmap'' (\x -> if isVariable x then variablePart x else x)) ct


getReduct :: TermTree -> TermTree -> [([Int],TermTree)]
getReduct t0 t1 =
  let disTree = pairTree t0 t1
      root = fromJust $ Map.lookup [] (mapping disTree)
      disMap = Map.filter (\(a,b) -> a /= b) (mapping disTree)
      funcVarMap = Map.filter (\(a,b) -> (not $ isVariable a) && (isVariable b)) disMap
      domains = Map.keys funcVarMap
      subTrees = map (ee . getSubCTree t0) domains
  in  if fst root /= snd root
      then []
      else zip domains subTrees

--------------------------------------------------------------------------------
--------------------------------Miscellaneous-----------------------------------
--------------------------------------------------------------------------------

incompleteWS = not . completeWS

-- Checks if a working set is a solution
completeWS :: WorkingSet -> Bool
completeWS (WS ct _ _ _ _) = completeCoInTree ct

-- Enumuerates the clauses in a program
enumProg = numberProg

leafFilter :: ([Int], CoInElem) -> Bool
leafFilter (_,(TT a)) = not $ isTrueTT a
leafFilter _ = False

notTrueTT = not . checkTrueTT

-- Checks if a termtree is the symbol for true
checkTrueTT :: ([Int], CoInElem) -> Bool
checkTrueTT (_,(TT (CTree _ d m))) =
  if length d == 1 && Map.elems m == ["◻"]
  then True
  else False
checkTrueTT (_,_) = False

fst3 (a,b,c) = a
snd3 (a,b,c) = b
thd3 (a,b,c) = c
