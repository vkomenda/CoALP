{-# LANGUAGE TypeOperators, FlexibleInstances, OverlappingInstances#-}

-- 18/07/2014
-- Reorganised Modules

module CoALP.CTree where

import Prelude hiding (foldr)

import Data.Tree
import Data.List
import Data.Maybe
import Data.Char
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (Foldable,foldr)
import Data.Ord (comparing)

type Domain = [[Int]]
type (-->) a b = Map a b
type RankedAlphabet a = ([a], a --> Int)

getRank :: (Ord a) => a -> RankedAlphabet a -> Maybe Int
getRank x (_, f) = Map.lookup x f

mergeRankAlpha :: (Ord a) => [RankedAlphabet a] -> RankedAlphabet a
mergeRankAlpha ras =
  let langs = map (fst) ras
      maps  = map (snd) ras
  in  (foldl union [] langs, Map.unions maps)

cleanRankAlpha :: (Ord a) => CTree a -> CTree a
cleanRankAlpha (CTree (l,a) d m) =
  let values = Map.elems m
      filteredLang = filter (\x -> x `elem` values) l
      filteredArity = Map.filterWithKey (\k _ -> k `elem` values) a
  in  CTree (filteredLang, filteredArity) d m

--------------------------------------------------------------------------------
-------------------------------CTree Definition---------------------------------
--------------------------------------------------------------------------------

-- Courcelle Tree
data CTree a = CTree {
    rankedAlpha :: RankedAlphabet a
  , domain      :: Domain
  , mapping     :: [Int] --> a
  } deriving (Eq, Ord)

empty :: CTree a
empty = CTree ([], Map.empty) [] Map.empty

--instance (Eq a) => Eq (CTree a) where
--  (==) (CTree _ d0 m0) (CTree _ d1 m1) = (sort d0) == (sort d1) && m0 == m1

-- Using mapKeysMonotonic here to avoid (Ord
-- need to rebuildRA after using fmap to ensure the RA is still valid
instance Functor CTree where
  fmap f (CTree (a,r) d m) = CTree (map f a, Map.mapKeysMonotonic f r) d (Map.map f m)

fmap'' :: (Ord a, Ord b) => (a -> b) -> CTree a -> CTree b
fmap'' f (CTree (a,r) d m) = CTree (map f a, Map.mapKeys f r) d (Map.map f m)

fmap''' :: (Ord a, Ord b) => (a -> b) -> CTree a -> CTree b
fmap''' f (CTree (a,r) d m) = CTree (map f a, Map.mapKeysWith max f r) d (Map.map f m)

instance Foldable CTree where
  foldr f z (CTree _ _ m) = Map.foldr f z m

-- Shows in a format with brakets between levels and commas between children
instance Show (CTree String) where
  show t = "CTree { " ++ convertToFnString [[]] t ++ " }"

-- The ranking and domain aren't hugely interesting most of the time. So I've just changed it to display the mapping for now.
instance (Show a) => Show (CTree a) where
  show (CTree _ _ m) = show m

-- Takes a Ranked Alphabet, a domain and a list of symbols (Ordered by domain -> symbol) and creates a CTree
-- Must be prefix closed ie you cannot have a prefix which itself is not a node
-- There cannont be any gaps in numbering ie 13 cannont be in the domain if 11 and 12 are not
-- Each domain value must map to some symbol
-- Nodes must have the correct number of children
safeCTree :: Ord a => RankedAlphabet a -> ([Int] --> a) -> Either String (CTree a)
safeCTree a m
  | prefixClosed domain == False          = Left ("The Domain is not prefix closed (1.2.1)")
  | succesiveDomain domain == False       = Left ("The Domain is not succesive (1.2.2)")
  | (validMappingArity a m) == False      = Left ("At least one node has invalid Arity (1.2.3)")
  | otherwise                             = Right (CTree a domain m)
  where domain = Map.keys m


-- SafeCTree except it takes a Domain and list of nodes rather than a mapping
safeCTreeFull :: Ord a => RankedAlphabet a -> Domain -> [a] -> Either String (CTree a)
safeCTreeFull a d m
  | prefixClosed d == False     = Left ("The Domain is not prefix closed (1.2.1)")
  | succesiveDomain d == False  = Left ("The Domain is not succesive (1.2.2)")
  | (length m) /= (length d)    = Left ("The list of symbols must be the same length as the domain")
  | (validArity a d m) == False = Left ("At least one node has invalid Arity (1.2.3)")
  | otherwise                   = Right (CTree a d (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip d m)))

-- Checks that the domain is prefix closed
prefixClosed :: (Eq a) => [[a]] -> Bool
prefixClosed xs =
  let parentOf x   = take (length x - 1) x
      hasParent xs = flip elem xs . parentOf
  in  and $ map (hasParent xs) xs


-- Checks that the domain contains sequential elements
succesiveDomain :: (Eq a, Num a) => [[a]] -> Bool
succesiveDomain xs =
  let predecessorOf x = init x ++ [(last x - 1)]
      hasPredecessor xs x
        | x == []     = True
        | last x == 1 = True
        | otherwise   = predecessorOf x `elem` xs
  in  and $ map (hasPredecessor xs) xs

-- Checks that no node has too many/few children
validArity :: Ord a => RankedAlphabet a -> Domain -> [a] -> Bool
validArity a d m =
  validArity' a d (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip d m))
  where validArity' _ [] _ = True
        validArity' r (x:xs) m
          | getRank (fromJust $ Map.lookup x m) r == Just (countChildren x m) = validArity' r xs m
          | otherwise                                                         = False

validMappingArity :: Ord a => RankedAlphabet a -> ([Int] --> a) -> Bool
validMappingArity (_, f) m =
  let domain   = Map.keys m
      ranks    = map (getRanks) domain
      getRanks = fromJust . flip Map.lookup f . fromJust . flip Map.lookup m
      children = map (flip countChildren m) domain
  in  ranks == children

--------------------------------------------------------------------------------
---------------------------------Infinte CTrees---------------------------------
--------------------------------------------------------------------------------

-- Work around for building trees with infinite segments or for constructing trees from the ground up.
-- Please note conversion from a incompleteCTree to a safeCTree is not guaranteed.
-- This means certain functions may not work on incompleteCTrees such as merging or getting a subTree.

-- Build an incomplete CTree, this uses a slightly different check for valid arity to allow for incomplete CTrees
incompleteCTree :: Ord a => RankedAlphabet a -> ([Int] --> a) -> Either String (CTree a)
incompleteCTree a m
  | prefixClosed domain == False          = Left ("The Domain is not prefix closed (1.2.1)")
  | succesiveDomain domain == False       = Left ("The Domain is not succesive (1.2.2)")
  | (incValidMappingArity a m) == False   = Left ("At least one node has invalid Arity (1.2.3)")
  | otherwise                             = Right (CTree a domain m)
  where domain = Map.keys m

incompleteCTreeFull :: Ord a => RankedAlphabet a -> Domain -> [a] -> Either String (CTree a)
incompleteCTreeFull a d m
  | prefixClosed d == False        = Left ("The Domain is not prefix closed (1.2.1)")
  | succesiveDomain d == False     = Left ("The Domain is not succesive (1.2.2)")
  | (length m) /= (length d)       = Left ("The list of symbols must be the same length as the domain")
  | (incValidArity a d m) == False = Left ("At least one node has invalid Arity (1.2.3)")
  | otherwise                      = Right (CTree a d (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip d m)))

incValidArity :: Ord a => RankedAlphabet a -> Domain -> [a] -> Bool
incValidArity a d m =
  incValidArity' a d (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip d m))
  where incValidArity' _ [] _ = True
        incValidArity' r (x:xs) m
          | getRank (fromJust $ Map.lookup x m) r >= Just (countChildren x m) = incValidArity' r xs m
          | otherwise                                                         = False

incValidMappingArity :: Ord a => RankedAlphabet a -> ([Int] --> a) -> Bool
incValidMappingArity (_, f) m =
  let domain   = Map.keys m
      ranks    = map (getRanks) domain
      getRanks = fromJust . flip Map.lookup f . fromJust . flip Map.lookup m
      children = map (flip countChildren m) domain
  in  ranks `allGTE` children

allGTE :: Ord a => [a] -> [a] -> Bool
allGTE (x:xs) (y:ys) = (x >= y) && (allGTE xs ys)
allGTE _ _ = True

incompleteCTreeToSafe :: (Ord a) => CTree a -> CTree a
incompleteCTreeToSafe t = ee $ safeCTree (rankedAlpha t) (mapping t)

--------------------------------------------------------------------------------
-------------------------------CTree Operations---------------------------------
--------------------------------------------------------------------------------

eqCTree :: (Ord a, Eq a) => CTree a -> CTree a -> Bool
eqCTree (CTree (a0, r0) d0 m0) (CTree (a1, r1) d1 m1) = (sort a0) == (sort a1) && r0 == r1 && (sort d0) == (sort d1) && m0 == m1

-- Find value in CTree, returns domains of value if found, otherwise empty list
findValueDomains :: (Ord a) => a -> CTree a -> [[Int]]
findValueDomains v t = Map.keys . Map.filter (== v) $ mapping t

containsValue :: (Ord a) => a -> CTree a -> Bool
containsValue v t
  | filteredMap == Map.empty = False
  | otherwise                = True
  where filteredMap = Map.filter (== v) $ mapping t

sameAsRoot :: (Eq a) => a -> CTree a -> Bool
sameAsRoot v (CTree _ _ m) = Just v == Map.lookup [] m

-- Merge the first CTree into the second at the Node specified
-- Both CTrees must share the same rankedAlphabet and the node must exist in t1
-- Also does not remove any children of existing node (assumed to be a leaf when merging)
mergeCTree :: (Ord a) => CTree a -> CTree a -> [Int] -> Either String (CTree a)
mergeCTree t0 t1 n =
  let toMergeMap   = Map.mapKeys (n ++) (mapping t0)
      mergedMap    = Map.union toMergeMap (mapping t1)
      mergedRA     = mergeRankedAlpha (rankedAlpha t0) (rankedAlpha t1)
  in  safeCTree mergedRA mergedMap

replaceNodesAt :: (Ord a) => CTree a -> CTree a -> [[Int]] -> CTree a
replaceNodesAt _ nt [] = nt
replaceNodesAt t0 t1 (d:ds) = replaceNodesAt t0 (ee $ mergeCTree t0 t1 d) ds

mergeRankedAlpha :: (Ord a) => RankedAlphabet a -> RankedAlphabet a -> RankedAlphabet a
mergeRankedAlpha (l0,ra0) (l1,ra1) =
  let newSymList = nub (l0 ++ l1)
      mergedMap  = Map.union ra0 ra1
  in  (newSymList, mergedMap)

-- Returns a subtree from the node specified
-- TODO - Could probably be done with just the mapping (filterWithKeys, mapKeys)..
getSubCTree :: Ord a => CTree a -> [Int] -> Either String (CTree a)
getSubCTree t n =
  let reducedDomain = filter (n `isPrefixOf`) (domain t)            -- Filters the domain into just the node specified and it's children
      symbolsList   = domainValues (mapping t) $ reducedDomain      -- Gets all the values of the domains
      subTreeDomain = map (fromJust . stripPrefix n) reducedDomain  -- Removes the prefix from all the domains
  in  safeCTreeFull (rankedAlpha t) subTreeDomain symbolsList       -- Creates a new CTree


-- gets the values associated with the domains passed
domainValues :: ([Int] --> a) -> Domain ->  [a]
domainValues m = map (getVals m)
  where getVals m = fromJust . flip Map.lookup m

-- Add Node to a CTree given the position of its parent node
-- Uses incompleteCTree as it can't ensue arity is equal until whole tree is added
addToCTree :: (Ord a) => CTree a -> [Int] -> a -> Either String (CTree a)
addToCTree t n v
  | Map.null (mapping t) = (either (addError n) Right (incompleteCTree (rankedAlpha t) (Map.insert [] v $ mapping t)))
  | isNode t n           = (either (addError n) Right (incompleteCTree (rankedAlpha t) (modifyMap n (mapping t) v)))
  | otherwise            = Left ("Node, "++ show n ++" could not be found")
    where modifyMap n m v = Map.insert (n ++ [(countChildren n m) + 1]) v m
          addError n s    = Left ("Error at node " ++ show n ++ "\n" ++ s)

-- Adds or replaces Node in a CTree given its position
-- Uses incompleteCTree as it can't ensue arity is equal until whole tree is added
addToCTree' :: (Ord a) => CTree a -> [Int] -> a -> Either String (CTree a)
addToCTree' t n v
  | Map.null (mapping t) = (either (addError n) Right (incompleteCTree (rankedAlpha t) (Map.insert [] v $ mapping t)))
  | otherwise            = (either (addError n) Right (incompleteCTree (rankedAlpha t) (Map.insert n v $ mapping t )))
    where addError n s    = Left ("Error at node " ++ show n ++ "\n" ++ s)

superAddToCTree :: (Ord a) => CTree a -> [Int] -> a -> Either String  (CTree a)
superAddToCTree ct@(CTree _ _ m) dom val
  | Map.null m = (either (addError dom) Right (incompleteCTree (newRA val) (Map.insert [] val m)))
  | otherwise  = (either (addError dom) Right (incompleteCTree (modRA ct dom val ) (modMap dom m val)))
    where modMap n m v = Map.insert (n ++ [(countChildren n m) + 1]) v m
          newRA v      = ([v], Map.insert v 0 Map.empty)
          addError n s = Left ("Error at node " ++ show n ++ "\n" ++ s)

removeFromTree :: (Ord a) => CTree a -> [Int] -> CTree a
removeFromTree ct@(CTree (l,a) d m) dom =
  let toRemove = filter (dom `isPrefixOf`) d
      newMap = Map.filterWithKey (\k _ -> k `notElem` toRemove) m
      newL   = Map.elems newMap
      newRA  = Map.filterWithKey (\k _ -> k `elem` newL) a
  in  CTree (newL,newRA) (Map.keys newMap) newMap

removeAndReplace :: (Ord a) => CTree a -> [Int] -> a -> Either String  (CTree a)
removeAndReplace ct@(CTree (l,a) d m) dom val =
  let toRemove = filter (dom `isPrefixOf`) d
      newMap = Map.insert dom val $ Map.filterWithKey (\k _ -> k `notElem` toRemove) m
      newL   = nub $ Map.elems newMap
      newRA  = Map.filterWithKey (\k _ -> k `elem` newL) a
      nRA    = case Map.lookup val newRA of
                 Just _ -> newRA
                 Nothing -> Map.insert val 0 newRA
  in  incompleteCTree (newL,nRA)  newMap


modRA :: (Ord a) => CTree a -> [Int] -> a -> RankedAlphabet a
modRA (CTree (l, a) _ m) d val
  | val `elem` l = (l, updateRA a parent newArity)
  | otherwise    = (l ++ [val], updateRA (Map.insert val 0 a) parent newArity)
  where parent   = fromJust $ Map.lookup d m
        newArity = (countChildren d m) + 1

updateRA :: (Ord a) => a --> Int -> a -> Int -> a --> Int
updateRA arity parent new = Map.update update parent arity
  where old      = fromJust $ Map.lookup parent arity
        update x = if new > old then Just new else Just old

-- Draw a 2D representation of the tree
drawCTree :: CTree [Char] -> IO ()
drawCTree = putStrLn . drawTree . cTreeToTree

-- Converts from a CTree to a Tree
cTreeToTree :: CTree [a] -> Tree [a]
cTreeToTree t = toTree (sort $ domain t) (mapping t)

toTree :: [[Int]] -> Map.Map [Int] [a] -> Tree [a]
toTree (x:[]) m = Node (fromJust (Map.lookup x m)) []
toTree (x:xs) m = Node (fromJust (Map.lookup x m)) (toForest (findChildren x m) xs m)

toForest :: [[Int]] -> [[Int]] -> Map.Map [Int] [a] -> Forest [a]
toForest [] _ _ = []
toForest (c:[]) xs m = [(toTree (c:xs) m)] ++ []
toForest (c:cs) xs m = [(toTree (c:xs) m)] ++ toForest cs xs m

-- Converts from a CTree to a List of values (flatten)
cTreeToList :: CTree a -> [a]
cTreeToList = Data.Foldable.foldr (:) []



-- show the tree in the bracket and comma seperated format
convertToFnString :: [[Int]] -> CTree String -> String
convertToFnString [] _ = []
convertToFnString _ (CTree _ [] _) = "Empty CTree"
convertToFnString (x:xs) t@(CTree _ _ m) =
  let curr = (fromJust $ Map.lookup x m)
      next = convertToFnString xs t
      chd  = childrenString x t
      nb   = neighbourString x t
  in curr ++ chd ++ nb ++ next

childrenString :: [Int] -> CTree String -> String
childrenString x t@(CTree _ _ m)
  | count > 0  = "(" ++ children ++ ")"
  -- | count == 1 = children
  | otherwise  = ""
    where count    = countChildren x m
          children = convertToFnString (findChildren x m) t

neighbourString :: [Int] -> CTree String -> String
neighbourString x t
  | hasNeighbour x t = ","
  | otherwise        = ""

replaceRA :: (Ord a) => CTree a -> RankedAlphabet a -> CTree a
replaceRA t ra = ee $ safeCTree ra (mapping t)

rebuildRA :: (Ord a) => CTree a -> CTree a
rebuildRA t@(CTree (l,r) _ m)
  | Map.valid r == False = ee $ safeCTree (l, Map.fromList $ Map.toList r) m
  | otherwise = t

raFromList :: (Ord a, Eq a) => [a] -> RankedAlphabet a
raFromList ls = (nub ls, Map.fromList ((zip (init ls) [1..]) ++ [(last ls, 0)]) )

fromList :: (Ord a, Eq a) => [a] -> CTree a
fromList ls =
  let ra = raFromList ls
      t = CTree ra [] Map.empty
  in  fromList' t ls 0

fromList' :: (Ord a, Eq a) => CTree a -> [a] -> Int -> CTree a
fromList' t lst@(l:ls) i
  | i == 0 = fromList' (ee $ addToCTree t [] l) ls (i+1)
  | lst == [] = t
  | otherwise = fromList' (ee $ addToCTree t [i] l) ls (i+1)


-- Produces a CTree which consists of all matching domains as pairs
pairTree :: (Ord a, Ord b) => CTree a -> CTree b -> CTree (a,b)
pairTree t0@(CTree (l0,a0) d0 m0) t1@(CTree (l1,a1) d1 m1) =
  let newDomain = d0 `intersect` d1
      t0Values = map (fromJust . flip Map.lookup m0) newDomain
      t1Values = map (fromJust . flip Map.lookup m1) newDomain
      newValues = zip t0Values t1Values
      newMap = (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip newDomain newValues))
      calcArity = map (flip countChildren newMap) newDomain
      arityMap = (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip newValues calcArity))
      rankedAlpha = (newValues, arityMap)
  in  ee $ safeCTree rankedAlpha newMap

-- Is t1 a subTree of t0
isSubTree :: (Ord a, Eq a) => CTree a -> CTree a -> Bool
isSubTree t0@(CTree (l0,a0) d0 m0) t1@(CTree (l1,a1) d1 m1) =
  let headT1 = fromJust $ Map.lookup [] m1
      domains = findValueDomains headT1 t0
      subTrees = map (ee . (getSubCTree t0)) domains
  in  or $ map (`eqCTreeLoose` t1) subTrees

-- Is t1 a subTree of t0
subTreeDom :: (Ord a, Eq a) => CTree a -> CTree a -> [[Int]]
subTreeDom t0@(CTree (l0,a0) d0 m0) t1@(CTree (l1,a1) d1 m1) =
  let headT1 = fromJust $ Map.lookup [] m1
      domains = findValueDomains headT1 t0
      subTrees = map (ee . (getSubCTree t0)) domains
      domSub = zip domains (map (`eqCTreeLoose` t1) subTrees)
      matchingDom = filter (\(a,b) -> b == True) domSub
  in  map (fst) matchingDom

eqCTreeLoose :: (Ord a, Eq a) => CTree a -> CTree a -> Bool
eqCTreeLoose (CTree _ d0 m0) (CTree _ d1 m1) = (sort d0) == (sort d1) && m0 == m1

--------------------------------------------------------------------------------
--------------------------------Node Operations---------------------------------
--------------------------------------------------------------------------------

-- Find all children of the node given a mapping, returns the domains of each node which is a child
findChildren :: [Int] -> ([Int] --> a) -> [[Int]]
findChildren x m = findChildren' x m 1
  where findChildren' x m a
          | (Map.member (x ++ [a]) m) = [(x ++ [a])] ++ (findChildren' x m (a+1))
          | otherwise                 = []

-- Not sure which of these I prefer.
findChildren'' :: [Int] -> ([Int] --> a) -> [[Int]]
findChildren'' x = Map.keys . Map.filterWithKey (isParentOf x)
isParentOf x k _ = x `isPrefixOf` k && Just 1 == (fmap length (stripPrefix x k))

findLeaves :: CTree a -> [[Int]]
findLeaves t@(CTree _ dom tm) = filter (isLeafM tm) dom

findLeavesValue :: CTree a -> [a]
findLeavesValue t = map (fromJust . getNodeValue t) (findLeaves t)

-- Counts the number of children each node has
countChildren :: [Int] -> ([Int] --> a) -> Int
countChildren xs m = countChildren' xs m 1
  where countChildren' xs m a
          | (Map.member (xs ++ [a]) m) = (countChildren' xs m (a+1)) + 1
          | otherwise                  = 0

-- Checks if node has one or more children
hasChild :: [Int] -> ([Int] --> a) -> Bool
hasChild xs m = Map.member (xs ++ [1]) m

hasChildD :: [Int] -> [[Int]] -> Bool
hasChildD d ds = or $ map (isPrefixOf d) ds

lastDomains :: [[Int]] -> [[Int]]
lastDomains ds = filter (\x -> not $ hasChildD x ds) ds

getChildren :: CTree a -> [Int] -> Int -> [a]
getChildren t@(CTree _ _ m) d i =
  let val = Map.lookup (d ++ [i]) m
  in  case val of
        Nothing -> []
        Just a  -> [a] ++ getChildren t d (i+1)

-- Checks if node has a neighbour
hasNeighbour :: [Int] -> CTree a -> Bool
hasNeighbour [] _ = False
hasNeighbour n t  = isNode t (neighbour n)

neighbour :: [Int] -> [Int]
neighbour n = (init n) ++ [(last n +1)]

-- Checks a node is a leaf
isLeaf ::  Domain -> [Int] -> Bool
isLeaf d x = (x ++ [1]) `notElem` d

isLeafM :: ([Int] --> a) -> [Int] -> Bool
isLeafM tm d = (d ++ [1]) `Map.notMember` tm

-- Find if Node exists in CTree
isNode :: CTree a -> [Int] -> Bool
isNode (CTree _ _ tm) n = Map.member n tm

-- Get node value in CTree
getNodeValue ::  CTree a -> [Int] -> Maybe a
getNodeValue (CTree _ _ tm) n = Map.lookup n tm

-- Get parent of a node
getParent :: [Int] -> [Int]
getParent = init

-- Sort the a list of lists by length of each list
lsort :: [[a]] -> [[a]]
lsort = sortBy (comparing length)

--------------------------------------------------------------------------------
-- Everything after this point is manipulations of CTrees not functions --------
-- or definitions --------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
---------------------------Parsing Def into a CTree-----------------------------
--------------------------------------------------------------------------------

-- Creates a cTree from a Def (pair of domain/domin functions and symbols), n is the minum for any domain functions and m is the max value
-- The cTree produced here will be incomplete as whatever min & maximum value there will be some trailing node
-- TODO nub is a bit of a stopgap here..
cTreeFromDef :: Ord a => Int -> Int -> RankedAlphabet a ->
                [(String,a)] -> Either String (CTree a)
cTreeFromDef min max ra def =
  let domain  = (nub $ domainFromDef def min max)
      symbols = symListFromDef def min max
  in incompleteCTreeFull ra domain symbols

-- Takes pairs of strings and another type, the minimum and maximum values for n and returns a list of domains
domainFromDef :: [(String,a)] -> Int -> Int -> [[Int]]
domainFromDef = generateDomains . map (fst)

-- Takes pairs of strings and another type, the minimum and maximum values for n and returns a list of symbols
symListFromDef :: [(String,a)] -> Int -> Int -> [a]
symListFromDef def min max = concat (map (symListFromDef' min max) def)
  where symListFromDef' min max p
          | 'n' `elem` (fst p) = replicate (max-min+1) (snd p)
          | otherwise          = [snd p]


-- This is for converting strings representing a function into a list of list of Ints
-- Ie 2n where min is 1 and max is 4 -> [[2,2,2,2],[2,2,2],[2,2],[2]]
-- Currently only supports one instance of n.


-- Generates a list of domains from a list of strings
generateDomains :: [String] -> Int -> Int -> [[Int]]
generateDomains [] _ _ = []
generateDomains (x:xs) min max
  | 'n' `elem` x = parseFN x min max ++ generateDomains xs min max -- If x is a function (as it contains an 'n')
  | otherwise    = [convertFn x] ++ generateDomains xs min max

-- Parses the whole String
parseFN :: String -> Int -> Int -> [[Int]]
parseFN a min max =
   let func     = mergeFn (splitFn a)
       prefixed = map (generatePrefix func ++) $ generateN func min max
       parsed   = map (++ generateSuffix func) $ prefixed
   in parsed

-- Splits the String into a list of strings
splitFn :: String -> [String]
splitFn (x:[]) = [[x]]
splitFn (x:xs) = [[x]] ++ (splitFn xs)

-- Merges any n statements with the number which will be repeated n times
mergeFn :: [String] -> [String]
mergeFn [] = []
mergeFn (x:[]) = [x]
mergeFn (x:y:xs)
  | y == "n"  = [x ++ y] ++ mergeFn xs
  | otherwise = [x] ++ mergeFn (y:xs)

-- generates the list of list of ints
generateN :: [String] -> Int -> Int -> [[Int]]
generateN [] _ _ = []
generateN (x:xs) n m
  | length x == 2 = takeNDomain n m (digitToInt (x !! 0))
  | otherwise     = generateN xs n m

-- generates the prefix for the list
generatePrefix :: [String] -> [Int]
generatePrefix [] = []
generatePrefix (x:xs)
  | length x == 1 = [read x] ++ generatePrefix xs
  | otherwise     = []

-- generates the suffix for the list
generateSuffix :: [String] -> [Int]
generateSuffix [] = []
generateSuffix (x:xs)
  | length x == 2 = generateSuffix' xs
  | otherwise     = generateSuffix xs
  where	generateSuffix'	[]     = []
        generateSuffix' (x:xs) = [read x] ++ generateSuffix' xs

-- Converts a String into a list of Ints
convertFn :: String -> [Int]
convertFn [] = []
convertFn (x:xs)
  | x == ','  = convertFn xs
  | otherwise = [digitToInt x] ++ convertFn xs

-- Adds a prefix to every list
addPrefix :: [a] -> [[a]] -> [[a]]
addPrefix x = map (x ++)

-- Creates a list of lists of ints going from largest to smallest
--  min number of reps, max number of reps, value to repeat
takeNDomain :: Int -> Int -> Int -> [[Int]]
takeNDomain n m x
  | m >= n    = [(replicate m x)] ++ (takeNDomain n (m-1) x)
  | otherwise = []

--------------------------------------------------------------------------------
-------------------Langauge Based Tree Generation-------------------------------
--------------------------------------------------------------------------------

-- Generates a set of Trees based on an alphabet and a list of nodes

completeCTree :: Ord a => CTree a -> CTree a
completeCTree t = either failedTree id $ safeCTree (rankedAlpha t) (mapping t)

langGen :: (Ord a) => RankedAlphabet a -> [a] -> [CTree a]
langGen r l = map (completeCTree) . nub . map (fst) . treeAdd $ prepGeneration r l

-- Get all CTree roots and associate with apropriate lists
prepGeneration :: Ord a => RankedAlphabet a -> [a] -> [(CTree a, [a])]
prepGeneration r vs = zip (prepTrees r (nub vs)) (dropFirst (nub vs) vs)
  where dropFirst [] l = []
        dropFirst (x:xs) l = [delete x l] ++ dropFirst xs l

-- Create CTrees with each element of the list as the root
prepTrees :: Ord a => RankedAlphabet a -> [a] -> [CTree a]
prepTrees _ [] = []
prepTrees r (d:ds) = [(ee $ addToCTree (CTree r [] Map.empty) [] d)] ++ prepTrees r ds

-- Add each element to all possible nodes in all trees
treeAdd :: (Ord a) => [(CTree a, [a])] -> [(CTree a, [a])]
treeAdd [] = []
treeAdd (t@(_,[]):xs) = [t] ++ treeAdd xs
treeAdd ((t,l):xs) = treeAdd(addElemToAll l t) ++ treeAdd xs

-- Add each element to all possible nodes in the tree
addElemToAll :: (Ord a) => [a] -> CTree a -> [(CTree a, [a])]
addElemToAll [] _ = []
addElemToAll xs t = addElemToAll' t xs (nub xs)
  where addElemToAll' _ _ [] = []
        addElemToAll' t l (x:xs) = addToAll l x t ++ addElemToAll' t l xs


-- Add the elemtn to all possible nodes in the tree
addToAll :: (Ord a) => [a] -> a -> CTree a -> [(CTree a, [a])]
addToAll l v t = map (\y -> (y, delete v l)) (filter (\x -> x /= CoALP.CTree.empty ) (addToAll' v t (domain t)))
  where addToAll' _ _ [] = []
        addToAll' v t (d:ds) = [either failedTree id (addToCTree t d v)] ++ addToAll' v t ds

failedTree :: String -> CTree a
failedTree _ = CoALP.CTree.empty

--------------------------------------------------------------------------------
--------------------Domain Based Tree Generation--------------------------------
--------------------------------------------------------------------------------
-- Idea here is to generate all possible domain permutations given a number of--
-- nodes, max arity and number of 0 arity nodes---------------------------------
--------------------------------------------------------------------------------

-- Check list of domains are valid
-- checkDomains (generateAllDomains 12 2 3)
checkDomains :: [Domain] -> Bool
checkDomains [] =  True
checkDomains (x:xs)
  | prefixClosed x && succesiveDomain x  = checkDomains xs
  | otherwise                            = False

-- Generate Domains for number of nodes, max arity and number of 0 arity nodes
generateAllDomains :: Int -> Int -> Int -> [Domain]
generateAllDomains n a b
  | (n < a+1) = concat $ mergeOverLists $ domainsFromLists $ trimAddList b n (generateAddList (n-1) n)
  | otherwise = concat $ mergeOverLists $ domainsFromLists $ trimAddList b n (generateAddList a n)
    where domainsFromLists = map (map generateStdDomain)
          mergeOverLists   = nub . map mergeDomainsOverList

-- Generate a single standard domain
generateStdDomain :: Int -> Domain
generateStdDomain a = [[]] ++ (fmap (:[]) $ take a [1..])

-- Need to merge the domains at every point where there is a node which has no child and return it as a list of domains.
-- Repeat for every element in the add list

mergeDomainsOverList :: [Domain] -> [Domain]
mergeDomainsOverList [] = []
mergeDomainsOverList (d:[]) = [d]
mergeDomainsOverList (d0:d1:[]) = mergeAllPoints d1 d0
mergeDomainsOverList (d0:d1:ds) = mergeDomainsOverList' (mergeAllPoints d1 d0) ds

mergeDomainsOverList' [] ys = []
mergeDomainsOverList' (d:ds) ys = mergeDomainsOverList (d:ys) ++ mergeDomainsOverList' ds ys

-- Merge the first domain into the second domain at each leaf
mergeAllPoints :: Domain -> Domain -> [Domain]
mergeAllPoints d0 d1 = map (mergeDomain d0 d1) $ filter (isLeaf d1) d1

-- Merge the first Domain into the second at the node specified
-- Does not remove any children of existing node assumed to be merging at a leaf
mergeDomain :: Domain -> Domain -> [Int] -> Domain
mergeDomain d0 d1 n = sort $ nub $ map (n ++) d0 ++ d1

-- Trim list based on number of nodes with 0 arrity
trimAddList :: Int -> Int -> [[Int]] -> [[Int]]
trimAddList x n l = filter (maxDepth x n) l
  where maxDepth x n k = (length k) <= n-x

-- Generate list of all possible permutations of numbers from 1 to m that add up to (n -1)
generateAddList :: Int -> Int -> [[Int]]
generateAddList 0 n = []
generateAddList m n = generateAddList' . nub $ addList m n
  where generateAddList' l = lsort $ (concat $ map (uniquePermutations) (init l)) ++ [last l]

-- Generate list of largest numbers which sum to m, and their permutations
-- Then do the same again for each of the numbers on the list.
-- TODO comments.. also seems like there is probably a better way to do this..
addList :: Int -> Int -> [[Int]]
addList 0 n = []
addList m n = addListAux m n (maxList m (n-1) []) ++ (addList (m-1) n)

addListAux :: Int -> Int -> [[Int]] -> [[Int]]
addListAux m n [] = []
addListAux m n p@((1:_):xs)  = p ++ (addListAux m n xs)                    -- When the first number is 1 move to next list of elements
addListAux m n p@((d:ds):xs) = p ++ (addListAux m n $ maxList (d-1) d ds)  -- Get the list of (d-1)s into d with ds as a suffix

-- Gets a list of ms, n divded by m long with the remainder on the end and the list of ints s
maxList :: Int -> Int -> [Int] -> [[Int]]
maxList m n s =
  let checkPos x = if x > 0 then [x] else []             -- List with the elemnt x if > 0, empty list otherwise
      maxDivisorList = replicate (n `quot` m) m          -- List of ms, n divided by m long
      remainderList  = checkPos $ n `mod` m              -- List of the remainder, if > 0
  in  [sortDesc $ maxDivisorList ++ remainderList ++ s]  -- List of elements sorted in a descending order

sortDesc :: Ord a => [a] -> [a]
sortDesc = sortBy (flip compare)

-- Borrowed from https://www.mail-archive.com/haskell-cafe@haskell.org/msg49360.html as a way of generating unique permutations
uniquePermutations :: Ord a => [a] -> [[a]]
uniquePermutations = Data.List.foldr (concatMap . inserts) [[]] . group . sort

inserts :: [a] -> [a] -> [[a]]
inserts [] ys = [ys]
inserts xs [] = [xs]
inserts xs@(x:xt) ys@(y:yt) = [x:zs | zs <- inserts xt ys]
                                ++ [y:zs | zs <- inserts xs yt]

ee = either error id
