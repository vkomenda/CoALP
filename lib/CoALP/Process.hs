module CoALP.Process where

import CoALP.CTree
import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.CoInTree
import CoALP.Substitution
import CoALP.UI.Parser
import CoALP.UI.Dot
import CoALP.UI.Printer
--import CT_CoALP.Process
--import CT_CoALP.Guards (gc3WSCheck)

import Data.List
import Data.Maybe
import Data.Functor.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Control.Monad.State.Lazy

type Solution = CoInTree
--type WorkState = State [WorkingSet]
type ClauseMap = Map Int String
type VarMap = Map.Map String Int
type Memory = [([Int],Reduct)]

data DSet = DS {  coTree'    :: CoInTree
                , parent'    :: CoInTree
                , prg'       :: Program
                , varMap'    :: VarMap
                , clMap'     :: ClauseMap
                , varCount'  :: Int
                , memory     :: Memory
               } deriving (Show, Ord, Eq)
data DElem = DElemDS DSet | DElemBool Bool deriving (Show, Ord, Eq)

instance ShowNoQ DElem where
  show0 (DElemDS ds) = show0 ds
  show0 (DElemBool b) = show0 b

instance ShowNoQ DSet where
  show0 ds@DS{coTree' = ct} = show0 ct

instance ShowNoQ Bool where
  show0 b = show b


type Queue = [[Int]]
type DTree = CTree DElem
type DState = State (Queue,DTree)

--------------------------------------------------------------------------------
---------------------------------D Set Operations-------------------------------
--------------------------------------------------------------------------------

initDS = DS { coTree'   = empty
            , parent'   = empty
            , prg'      = []
            , varMap'   = Map.empty
            , clMap'    = Map.empty
            , varCount' = 0
            , memory    = [dummyReduct] 
            }

initGoal :: Goal -> CoInTree
initGoal g =
  let goalList = map (convertToFnString [[]]) g
      stringGoal = "endGoal: " ++ (concat $ (map (++ ",") (init goalList))) ++ last goalList
  in  makeCoInTree ([makeTermTree (Map.insert [] stringGoal  Map.empty)] ++ g)

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

dummyReduct :: ([Int],Reduct)
dummyReduct = ([-1],(-1,[([], empty)]))

fromDElemBool :: DElem -> Maybe Bool
fromDElemBool (DElemBool a) = Just a
fromDElemBool _             = Nothing

fromDElemDS :: DElem -> Maybe DSet
fromDElemDS (DElemDS a) = Just a
fromDElemDS _           = Nothing

initialDTree :: DElem -> DTree
initialDTree ds = 
  let lang   = [ds]
      arity  = Map.insert ds 0 Map.empty
      domain = [[]]
      map    = Map.insert [] ds Map.empty
  in  CTree (lang, arity) domain map

getDSet :: DTree -> [Int] -> DSet
getDSet (CTree _ _ m) d = (fromJust $ fromDElemDS $ fromJust $ Map.lookup d m)

getDerivationChain :: DTree -> [Int] -> [([Int],DSet)]
getDerivationChain _ [] = []
getDerivationChain dt d = [(d,getDSet dt d)] ++ getDerivationChain dt (init d)

eqDSet :: DSet -> DSet -> Bool
eqDSet DS{coTree' = ct0} DS{coTree' = ct1} = eqCoIn ct0 ct1

--------------------------------------------------------------------------------
-------------------------------Process Operations-------------------------------
--------------------------------------------------------------------------------

firstTime :: ([ClauseTree], [[TermTree]], [String]) -> ([[Int]], DTree)
firstTime items@(pr, (g:gs), cots) = 
  let ds         = initDS {parent' = (initGoal g), coTree' = (initGoal g), prg' = pr, clMap' = (cotsToCM pr cots)}
      initDTree  = initialDTree (DElemDS ds)
      inDS       = fullTermMatchDS [ds] [ds]
      incTM      = filter (incompleteDS) inDS
      compTM     = filter (completeDS) inDS
      inc        = map (\x -> x {parent' = coTree' x}) incTM
      gc3ed      = gc3DSCheck gc3TestDS inc
      toAdd      = compTM ++ gc3ed
      newDTree   = addDStoDT initDTree [] toAdd 
      newDomains = if toAdd == []
                   then [[1]]
                   else map (\x -> [x]) [1..(length toAdd)]
  in  (newDomains, newDTree)

findNextSolutionDS :: ([[Int]] -> [[Int]] -> [[Int]]) -> ([ClauseTree], [[TermTree]], [String]) -> (Queue,DTree) -> ([[Int]],(Queue,DTree))
findNextSolutionDS prioF items@(pr, (g:gs), cots) ([],dt)
  | dt == empty = findNextSolutionDS prioF items (firstTime items)
  | otherwise   = ([],([],dt))
findNextSolutionDS prioF _ (q,dt) = runState (nextSolutionDS prioF) (q,dt)

findNextSolutionDS' :: Int -> ([[Int]] -> [[Int]] -> [[Int]]) -> ([ClauseTree], [[TermTree]], [String]) -> (Queue,DTree) -> ([[Int]],(Queue,DTree))
findNextSolutionDS' n prioF items@(pr, (g:gs), cots) ([],dt)
  | dt == empty = findNextSolutionDS' n prioF items (firstTime items)
  | otherwise   = ([],([],dt))
findNextSolutionDS' n prioF _ (q,dt) = runState (nextSolutionDS' n prioF) (q,dt) 

saveNDS :: Int -> Int -> ([[Int]] -> [[Int]] -> [[Int]]) -> ([ClauseTree], [[TermTree]], [String]) -> IO ()
saveNDS c m prioF items
  | c == m = return ()
  | otherwise = do 
                findNSave m prioF items ([],empty)
                saveNDS c (m+1) prioF items


findNSave :: Int -> ([[Int]] -> [[Int]] -> [[Int]]) -> ([ClauseTree], [[TermTree]], [String]) -> (Queue,DTree) -> IO ()
findNSave n prioF items@(pr, (g:gs), cots) ([],dt)
  | dt == empty = findNSave n prioF items (firstTime items)
  | otherwise   = return ()
findNSave n prioF _ (q,dt) = saveFile ("DTree-" ++ show n) $ snd $ snd $ runState (nextSolutionDS' n prioF) (q,dt) 

nextSolutionDS' :: Int -> ([[Int]] -> [[Int]] -> [[Int]]) -> StateT (Queue,DTree) Data.Functor.Identity.Identity ([[Int]])
nextSolutionDS' 0 _ = return []
nextSolutionDS' n prioF = do
  sol <- processStep prioF
  (q,dt) <- get
  if sol /= []
  then return sol
  else if q /= []
       then nextSolutionDS' (n-1) prioF
       else return []

nextSolutionDS :: ([[Int]] -> [[Int]] -> [[Int]]) -> StateT (Queue,DTree) Data.Functor.Identity.Identity ([[Int]])
nextSolutionDS prioF = do
  sol <- processStep prioF
  (q,dt) <- get
  if sol /= []
  then return sol
  else if q /= []
       then nextSolutionDS prioF
       else return []

checkSolutions :: DTree -> [[Int]] -> [([Int], Bool)]
checkSolutions (CTree _ _ m) ds =
  let potentialSols = map (\x -> fromJust $ Map.lookup x m) ds
      results       = map (\x -> fromJust $ fromDElemBool x) potentialSols
  in  zip ds results
      

processStep :: ([[Int]] -> [[Int]] -> [[Int]]) -> DState ([[Int]])
processStep prioF = do
  (queue@(curr:rest),dtree@(CTree _ _ m)) <- get
  let nextDSet = fromJust $ Map.lookup curr m
  case nextDSet of
    DElemBool v -> do 
      put $ (rest,dtree)
      if v
      then return [(init curr)]--return [(fromJust $ fromDElemDS $ fromJust $ Map.lookup (init curr) m)]
      else return []
    DElemDS  ds -> do --
      let unified     = unifyDS unify ds
          dTreeUN     = if unified == [] && (not $ completeCoInTree (coTree' ds)) 
                        then (ee $ superAddToCTree dtree curr (DElemBool False))
                        else dtree
          incUN       = filter (incompleteDS) unified
          compUN      = filter (completeDS) unified
          termMatched = fullTermMatchDS incUN incUN
          incTM       = filter (incompleteDS) termMatched
          compTM      = filter (completeDS) termMatched
          gc3ed       = gc3DSCheck gc3TestDS incTM
          toAdd       = compUN ++ compTM ++ gc3ed
          newDTree    = addDStoDT dTreeUN curr toAdd 
          newDomains  = if toAdd == []
                        then [curr ++ [1]]
                        else map (\x -> curr ++ [x]) [1..(length toAdd)]
      put $ (prioF rest newDomains, newDTree)
      return ([])

prioDepthFirst :: [[Int]] -> [[Int]] -> [[Int]]
prioDepthFirst oldQ toAdd = toAdd ++ oldQ

prioBreadthFirst :: [[Int]] -> [[Int]] -> [[Int]]
prioBreadthFirst oldQ toAdd = oldQ ++ toAdd 

addDStoDT :: DTree -> [Int] -> [DSet] -> DTree
addDStoDT dt d [] = dt
addDStoDT dt d (ds@DS {coTree' = ct}:dss) = 
  let newTree = ee $ superAddToCTree dt d (DElemDS ds)
      numChildren = countChildren d (mapping newTree)
  in if completeCoInTree ct
     then addDStoDT (ee $ superAddToCTree newTree (d ++ [numChildren]) (DElemBool True)) d dss
     else addDStoDT newTree d dss

--unifyWSs' :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
--         DSet -> DSet
--unifyWSs' f ws = map (\x -> (x, unifyWS f x)) ws

-- Processes a list of working sets and returns the next list of working sets
--unifyWSs :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
--         [WorkingSet] -> [WorkingSet]
--unifyWSs f ws = nubBy (eqWS) $ concat $ map (unifyWS f) ws

--------------------------------------------------------------------------------
----------------------------------Unification-----------------------------------
--------------------------------------------------------------------------------

-- Processes a single working set
unifyDS :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->	
         DSet -> [DSet]
unifyDS f ds@DS { coTree' = ct, prg' = pr, varMap' = vm, clMap' = cm, varCount' = vc} = 
  let gls = filter (leafFilter) (zip (findLeaves ct) (findLeavesValue ct))
      domains = map (fst) gls
      leaves = coInElemToTT $ map (snd) gls
      program = runState (renameProgWithCT pr ct) vm
      idxPrg = (enumProg (fst program))
      substs = map (findClauseSubst f idxPrg ) leaves
      prioritized = prioritiseInductive cm (zip domains substs)
      newCoTs = map (applyUnify idxPrg ct vc) prioritized
      newDS = ds {parent' = ct, prg' = fst program, varMap' = snd program, clMap' = cm}
  in  map (\(n,x) -> newDS {coTree' = x, varCount' = n}) $ concat newCoTs

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
----------------------------------Term match------------------------------------
--------------------------------------------------------------------------------

-- Fully matches terms in a working set until no more matches can be made
fullTermMatchDS :: [DSet] -> [DSet] ->  [DSet]
fullTermMatchDS []   prev = prev
fullTermMatchDS curr prev = fullTermMatchDS (termMatchDSs termMatch curr) curr

-- Processes a list of working sets and returns the next list of working sets
termMatchDSs :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->
         [DSet] -> [DSet]
termMatchDSs f ds = nubBy (eqDS) $ concat $ map (termMatchDS f) ds

-- For term matching
termMatchDS :: (TermTree -> TermTree -> Either String (Subst, TermTree)) ->	
         DSet -> [DSet]
termMatchDS f ds@DS { coTree' = ct, prg' = pr, varMap' = vm, clMap' = cm, varCount' = vc} = 
  let gls = filter (leafFilter) (zip (findLeaves ct) (findLeavesValue ct))
      domains = map (fst) gls
      leaves = coInElemToTT $ map (snd) gls
      program = runState (renameProgWithCT pr ct) vm
      idxPrg = (enumProg (fst program))
      substs = map (findClauseSubst f idxPrg) leaves
      newCoTs = map (applyTermMatch idxPrg ct vc) (zip domains substs)
      newDS = ds {prg' = fst program, varMap' = snd program, clMap' = cm}
  in  map (\(n,x) -> newDS {coTree' = x, varCount' = n}) $ concat newCoTs

-- Apply the substitutions to a CoTree
applyTermMatch :: [(Int, ClauseTree)] -> CoInTree ->  Int -> ([Int], [(Int, Subst)]) -> [(Int, CoInTree)]
applyTermMatch _ _ _ (_,[]) = []
applyTermMatch prog t vc (d,(sub@(i, _):subs)) = 
  let (nvc, substAdded) = addSubst (vc, t) (length prog) d sub
      terms = getChildren (substClause prog sub) [] 1
      termAdded = addTerms substAdded terms (d ++ [i]) 
  in  [(nvc, cleanRankAlpha $ termAdded)] ++ applyTermMatch prog t vc (d,subs)

--------------------------------------------------------------------------------
--------------------------------GC3 Termination---------------------------------
--------------------------------------------------------------------------------

-- Performs GC3 across a set of parents and children
gc3DSCheck :: (DSet -> DSet) -> [DSet] -> [DSet]
gc3DSCheck gc3Func dss = map gc3Func dss

gc3TestDS :: DSet -> DSet
gc3TestDS ds@DS {memory = mem, coTree' = ct, clMap' = cm} =
  let reducts = gc3reductDS ds
      (nct, newMem) = checkReduct ct cm mem reducts
  in  ds {coTree' = nct, memory = newMem}

gc3TestDS' :: DSet -> DSet
gc3TestDS' ds@DS {memory = mem, coTree' = ct, clMap' = cm} =
  let reducts = gc3reductDS ds
      (nct, newMem) = checkReduct' ct cm mem reducts
  in  ds {coTree' = nct, memory = newMem}


gc3reductDS :: DSet -> [([Int],Reduct)]
gc3reductDS ds@DS {parent' = par, coTree' = child, prg' = program } =
  let prog = map (reduceVars) (program)
      domainDiff = (domain child) \\ (domain par)
      difference = map (fromJust . flip Map.lookup (mapping child)) domainDiff
      subs = map (subsHelper) $ filter (\(_,b) -> isCoInXSub b) (zip domainDiff difference)
      clauseProjection = catCP $ map (\(newNodeD,sub) -> (newNodeD,getClauseProjection prog par (init newNodeD) (fst sub)) ) subs
      loops = catLoops $ map (\(newNodeD,(clauseNum,reduct)) -> (newNodeD,(clauseNum,reduct),checkIfLoop child (init newNodeD) clauseNum)) clauseProjection
      coRecursiveReduct = map (\(newNodeD,xreduct,loopNode) -> (newNodeD,xreduct,loopNode,getCoRecurReduct child loopNode newNodeD) ) loops
      chreducts = map (\(newNodeD,xreduct,loopNode,coRecReducts) -> (newNodeD, checkForReductMatch xreduct coRecReducts) ) coRecursiveReduct
  in  chreducts

debugGC3reduct :: DSet -> IO ()
debugGC3reduct ds@DS {parent' = par, coTree' = child, prg' = program } = do
  let prog = map (reduceVars) (program)
      domainDiff = (domain child) \\ (domain par)
      difference = map (fromJust . flip Map.lookup (mapping child)) domainDiff
      subs = map (subsHelper) $ filter (\(_,b) -> isCoInXSub b) (zip domainDiff difference)
      clauseProjection = catCP $ map (\(newNodeD,sub) -> (newNodeD,getClauseProjection prog par (init newNodeD) (fst sub)) ) subs
      loops = catLoops $ map (\(newNodeD,(clauseNum,reduct)) -> (newNodeD,(clauseNum,reduct),checkIfLoop child (init newNodeD) clauseNum)) clauseProjection
      coRecursiveReduct = map (\(newNodeD,xreduct,loopNode) -> (newNodeD,xreduct,loopNode,getCoRecurReduct child loopNode newNodeD) ) loops
      chreducts = map (\(newNodeD,xreduct,loopNode,coRecReducts) -> (newNodeD, checkForReductMatch xreduct coRecReducts) ) coRecursiveReduct
  putStrLn $ "prog: " ++ show prog
  putStrLn $ "domainDiff: " ++ show domainDiff
  putStrLn $ "difference: " ++ show difference 
  putStrLn $ "subs: " ++ show subs
  putStrLn $ "clauseProjection: " ++ show clauseProjection
  putStrLn $ "loops: " ++ show loops
  putStrLn $ "coRecursiveReduct: " ++ show coRecursiveReduct
  putStrLn $ "chreducts: " ++ show chreducts

checkReduct :: CoInTree -> ClauseMap -> Memory -> [([Int],Reduct)] -> (CoInTree,Memory)
checkReduct ct cm mem [] = (ct, mem)
checkReduct ct cm mem ((d,reduct):reducts) =
  let matches = filter (\(a,b) ->  init a /= init d && b == reduct && snd b /= []) mem
      --parentD = init d
      --childrenD = sharedPredChild d ct
  in if matches /= [] && Map.lookup (fst reduct) cm == Just "c"
     then --checkReduct' (boxBranches' (ct) [d]) cm mem reducts
          checkReduct (boxBranches (addReduct ct [d] [reduct]) [d]) cm mem reducts
          --checkReduct' (boxBranches' ct [d]) cm mem reducts
     else checkReduct ct cm (mem ++ [(d,reduct)]) reducts

checkReduct' :: CoInTree -> ClauseMap -> Memory -> [([Int],Reduct)] -> (CoInTree,Memory)
checkReduct' ct cm mem [] = (ct, mem)
checkReduct' ct cm mem ((d,reduct):reducts) =
  let matches = filter (\(a,b) ->  init a /= init d && b == reduct && snd b /= []) mem
      --parentD = init d
      --childrenD = sharedPredChild d ct
  in if matches /= []
     then --checkReduct' (boxBranches' (ct) [d]) cm mem reducts
          checkReduct (boxBranches (addReduct ct [d] [reduct]) [d]) cm mem reducts
          --checkReduct' (boxBranches' ct [d]) cm mem reducts
     else checkReduct ct cm (mem ++ [(d,reduct)]) reducts

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
      node = Map.lookup d (mapping ct)
      treeTerm = fromJust $ fromTT $ fromJust $ node
      reduct = case node of
                 Nothing -> []
                 Just _  -> getReduct clauseTerm treeTerm
  in  if reduct /= []
      then Just (cn, reduct)
      else Nothing


-- getCoRecurReduct child loopNode newNodeD

getCoRecurReduct :: CoInTree -> [Int] -> [Int] -> [([Int],TermTree)]
getCoRecurReduct ct d0 d1 = 
  --case getCoRecursiveReduct ct d0 d1 of
  --  Just a -> a
  --  Nothing -> []6
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
--------------------------------Miscellaneous-----------------------------------
--------------------------------------------------------------------------------

incompleteDS = not . completeDS

-- Checks if a working set is a solution
completeDS :: DSet -> Bool
completeDS (DS {coTree' = ct}) = completeCoInTree ct

eqDS :: DSet -> DSet -> Bool
eqDS (DS {coTree' = ct0}) (DS {coTree' = ct1}) = ct0 `eqCoIn` ct1

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
