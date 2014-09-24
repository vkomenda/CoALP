-- 21/07/2014
-- Bug fix for some ranked alphabet issues

module CoALP.ClauseTree where

import Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.List (sortBy, sort, nubBy, unionBy)

import CoALP.CTree
import CoALP.TermTree

type ClauseTree = CTree TermTree
type Program = [ClauseTree]
type Goal = [TermTree]


-- Constructs a Clause tree from a list of term trees
makeClauseTree :: [TermTree] -> ClauseTree
makeClauseTree ts =
  let numTerms = length ts
      domain = generateStdDomain numTerms
      map = (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip domain ts))
      arityMap = (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip ts ([numTerms-1] ++ [0,0..])))
      rankedAlpha = (ts, arityMap)
  in  ee $ safeCTree rankedAlpha map

--------------------------------------------------------------------------------
----------------------------Clause Tree Operations------------------------------
--------------------------------------------------------------------------------

-- Get the head of a clause
clHead :: ClauseTree -> TermTree
clHead (CTree _ _ m) = fromJust (Map.lookup [] m)

-- Get the body of a clause
clBody  :: ClauseTree -> [TermTree]
clBody (CTree _ _ m) = clBody' m 1
  where clBody' m c = 
          case Map.lookup [c] m of
               Nothing -> [] 
               Just x  -> [x] ++ clBody' m (c+1)

-- Get the body of the ith Clause and enumerates each term in the body
clBodyI :: Program -> Int -> [(Int, TermTree)]
clBodyI pr i = zip [0..] (clBody $ pr !! i)

-- Get all the variables in the Clause Tree
varsClause :: ClauseTree -> [String]
varsClause (CTree _ _ m) = concat $ map (varsTerm) (Map.elems m)

-- Merge the first Clause Tree into the second at the Node specified
-- The node must exist in t1
-- Also does not remove any children of existing node (assumed to be a leaf when merging)
-- merges the RA of underlying term trees.. (clumsy)
-- To avoid perhaps strip variables to just the prefix before checkig arity? ie "X_2 = X"?
mergeClauseTree :: ClauseTree -> ClauseTree -> [Int] -> Either String ClauseTree
mergeClauseTree t0 t1 n =
  let newRA        = mergeCTRA ([t0] ++ [t1])
      newt0        = replaceCLTreeRA t0 newRA
      newt1        = replaceCLTreeRA t1 newRA
      toMergeMap   = Map.mapKeys (n ++) (mapping newt0)
      mergedMap    = Map.union toMergeMap (mapping newt1)
      mergedRA     = mergeClauseTRA (rankedAlpha newt0) (rankedAlpha newt1)
      newTree      = incompleteCTree mergedRA mergedMap
  in  newTree

-- Ignores the ranked alphabet part for the comparison
eqTermTree :: TermTree -> TermTree -> Bool
eqTermTree (CTree _ d0 m0) (CTree _ d1 m1) = (sort d0) == (sort d1) && m0 == m1

eqTermTree' (t0,i0) (t1,i1) = eqTermTree t0 t1

mergeClauseTRA :: RankedAlphabet TermTree -> RankedAlphabet TermTree -> RankedAlphabet TermTree
mergeClauseTRA (l0,ra0) (l1,ra1) =
  let newSymList = nubBy eqTermTree (l0 ++ l1)
      mergedMap  = Map.fromList $ unionPair eqTermTree (Map.toList ra0) (Map.toList ra1)
  in  (newSymList, mergedMap)

--unionRA :: RankedAlphabet a -> RankedAlphabet a -> RankedAlphabet a
--unionRA (l0,r0) (l1,r1) =
--  let arityList0 = Map.toList ra0
 --     arityList1 = Map.toList ra1
 --     mergedList = arityList0 ++ arityList1
      

--unionBy'                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
--unionBy' eq xs ys        =  xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

--unionPair'  :: ((a,b) -> (a,b) -> Bool) -> [(a,b)] -> [(a,b)] -> [(a,b)]
--unionPair' eq xs ys =
--  let mergeList = mergePairs xs ys

unionPair :: (Ord b) => (a -> a -> Bool) -> [(a,b)] -> [(a,b)] -> [(a,b)]
unionPair _  p0 []     = p0
unionPair eq p0 (p:ps) = unionPair eq (mergePairBy' eq p0 p) ps

mergePairBy' :: (Ord b) => (a -> a -> Bool) -> [(a,b)] -> (a,b) -> [(a,b)]
mergePairBy' _  []             p1         = [p1]
mergePairBy' eq (p0@(a0,b0):ps) p1@(a1,b1)
  | a0 `eq` a1 && b0 >= b1 = [p0] ++ ps
  | a0 `eq` a1 && b0 <= b1 = [p1] ++ ps
  | otherwise              = [p0] ++ mergePairBy' eq ps p1

mergePairBy :: (Ord b) => (a -> a -> Bool) -> (a,b) -> (a,b) -> [(a,b)]
mergePairBy eq p0@(a0,b0) p1@(a1,b1) 
  | a0 `eq` a1 && b0 >= b1 = [p0]
  | a0 `eq` a1 && b0 <= b1 = [p1]
  | otherwise              = [p1] ++ [p0]

-- Perform all possible direct merges for clauses in the program
-- Maybe can do this using fmap?
mergeProg :: Program -> Program
mergeProg p =
  let nP = sortBy (compareChildren) $ numberProg p
      merged = sortBy (compareFirst) $ mergingProg nP 0
  in  map (snd) merged

mergingProg :: [(Int,ClauseTree)] -> Int -> [(Int,ClauseTree)]
mergingProg cs i 
  | length cs > i = mergingProg newProg (i+1)
  | otherwise     = cs
  where merged  = mergeClause (snd $ cs !! i) cs
        newProg = replaceClause (sortBy compareFirst merged) cs


replaceClause :: [(Int, ClauseTree)] -> [(Int,ClauseTree)] -> [(Int,ClauseTree)]
replaceClause [] xs = xs
replaceClause _ [] = []
replaceClause p@((a0,c0):cs) (x@(a1,c1):xs)
  | a0 == a1  = [(a0,c0)] ++ replaceClause cs xs 
  | otherwise = [x] ++ replaceClause p xs


mergeClause :: ClauseTree -> [(Int,ClauseTree)] -> [(Int,ClauseTree)]
mergeClause ct cts =
  let mergePoints = findBodies (clHead ct) cts
      mergeDomains = map (findValueDomains (clHead ct)) (map snd mergePoints)
      merges = zip mergeDomains mergePoints
  in  performMerges ct merges

performMerges :: ClauseTree -> [([[Int]], (Int,ClauseTree))] -> [(Int,ClauseTree)]
performMerges ct [] = []
performMerges ct (m:ms) = [mergeAll ct m] ++ performMerges ct ms

mergeAll :: ClauseTree -> ([[Int]], (Int,ClauseTree)) -> (Int,ClauseTree)
mergeAll _ ([],t) = t
mergeAll ct ((x:xs),(i,t)) =  mergeAll ct (xs,(i,(ee $ either (addError t ct x) Right (mergeClauseTree ct t x))))
  where addError t ct x e = Left( e ++ "\n" ++ "Error merging at " ++ show x ++ "\n" ++ "Merging tree " ++ show t ++ "\n" ++ "Into tree " ++ show ct)

-- Finds the clauses whoese body contains the terms
findBodies :: TermTree -> [(Int,ClauseTree)] -> [(Int,ClauseTree)]
findBodies t cts =filter (containsBody t) cts
  where containsBody t (_,ct) = t `elem` (clBody ct)
  
-- Finds the clauses whoese heads match the terms
findHeads :: [TermTree] -> [ClauseTree] -> [(TermTree, [ClauseTree])]
findHeads ts cts = zip ts (map (flip findHead cts) ts)

-- Finds the clauses whoese heads match the term
findHead :: TermTree -> [ClauseTree] -> [ClauseTree]
findHead t cts = filter (containsHead t) cts
  where containsHead t ct =  t == clHead ct

-- Checks if the body of a clause contains the root of the head of the clause
headInBody :: ClauseTree -> Bool
headInBody ct =
  let head = tHead $ clHead ct
      body = clBody ct
  in  if body == []
      then False
      else or $ map (sameAsRoot head) body
	
-- Filters all the terms in the clause which contain the leading term in the head
termsWithHead :: ClauseTree -> [TermTree]
termsWithHead ct =
  let head = tHead $ clHead ct
      body = clBody ct
  in  filter (sameAsRoot head) body

-- Enumerates a list of clauses
numberProg :: Program -> [(Int,ClauseTree)]
numberProg = zip [1..]

-- Provides ordering based on the number of children the root of each clause tree has
compareChildren :: (Ord a) => (a,ClauseTree) -> (a,ClauseTree) -> Ordering
compareChildren (a0, t0) (a1, t1)
  | countChildren [] (mapping t0) < countChildren [] (mapping t1) = LT
  | countChildren [] (mapping t0) > countChildren [] (mapping t1) = GT
  | countChildren [] (mapping t0) == countChildren [] (mapping t1) = compare a0 a1

-- Provides ordering based only on the first value of a pair
compareFirst :: (Ord a) => (a,b) -> (a,b) -> Ordering
compareFirst (a0,b0) (a1,b1)
  | a0 < a1 = LT
  | a0 > a1 = GT
  | a0 == a1 = EQ

sortMerges :: [([[Int]], [ClauseTree])] -> [([[Int]], [ClauseTree])]
sortMerges = sortBy sortMerge  

sortMerge :: (t, [ClauseTree]) -> (t1, [ClauseTree]) -> Ordering
sortMerge (_, []) _ = GT
sortMerge _ (_, []) = LT
sortMerge (a1, b1) (a2, b2)
  | length (clBody $ head b1) < length (clBody $ head b2)  = GT
  | length (clBody $ head b1) > length (clBody $ head b2)  = LT
  | length (clBody $ head b1) == length (clBody $ head b2) = EQ


-- Merges all ranked alphabets in the term trees of a list of clause trees into a single ranked alphabet
mergeCTRA :: [ClauseTree] -> RankedAlphabet String
mergeCTRA cts = mergeRankAlpha $ map (mergeRankAlpha) $ getTermsFromCT cts

-- Gets all the ranked alaphabets from the term trees of a list of clause trees
getTermsFromCT :: [ClauseTree] -> [[RankedAlphabet String]]
getTermsFromCT cts = map (map rankedAlpha) $ map (getTermTrees) cts
  where getTermTrees (CTree (a,_) _ _) = a

-- Replaces the ranked alphabets of the term trees in a clause tree
replaceCLTreeRA :: ClauseTree -> RankedAlphabet String -> ClauseTree
replaceCLTreeRA ct ra = fmap (flip replaceRA ra) ct

--------------------------------------------------------------------------------
------------------------------Displaying Clause Tree----------------------------
--------------------------------------------------------------------------------

-- Displays the ClauseTree as a clause
drawClause :: ClauseTree ->  IO ()
drawClause = putStrLn . clauseTreeToString

-- Converts a ClauseTree into a Clause
clauseTreeToString :: ClauseTree -> String
clauseTreeToString t = 
  let treeList = cTreeToList (ppClauseTree t)
      root = head treeList
      rest = tail treeList
  in  if rest == []
      then root ++ "."
      else root ++ " :- " ++ commaSep rest ++ "."

--------------------------------------------------------------------------------
----------------------Displaying Program and Goals------------------------------
--------------------------------------------------------------------------------

-- Displays the Program as clauses
drawProgram :: Program -> IO ()
drawProgram p = putStrLn $ concat $ map (++ "\n") $ map clauseTreeToString p

-- Displays the goal
drawGoals :: [Goal] -> IO ()
drawGoals gs = putStrLn $ concat $ map goalToString gs

goalToString :: Goal -> String
goalToString g = ":- " ++ commaSep (map termTreeToString g) ++ ".\n"

--------------------------------------------------------------------------------
----------------------------Pretty Printing-------------------------------------
--------------------------------------------------------------------------------

-- Easier to read representation of a clause tree
ppClauseTree :: ClauseTree -> CTree String
ppClauseTree = fmap termTreeToString

-- Easier to read representation of a program
ppProg :: [ClauseTree] -> [CTree String]
ppProg = map ppClauseTree
