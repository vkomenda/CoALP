{-# LANGUAGE FlexibleInstances #-}

module CoALP.CoInTree where

import CoALP.CTree	
import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.Substitution
import CoALP.UI.Dot
import CoALP.UI.Printer

import Data.List (sort, nub)
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

-- TODO fix variable numbering so that it is consistent..

data CoInElem = XSub XSubst | TT TermTree | S String | Rdt Reduct deriving (Show, Ord, Eq)
type XSubst = (Int,Subst)
type CoInTree = CTree CoInElem
type GoalTree = CTree TermTree
type Reduct = (Int,[([Int], TermTree)])

instance ShowNoQ CoInElem where
  show0 (TT t) = show0 t
  show0 (XSub sub) = show0 sub
  show0 (S str) = show0 str
  show0 (Rdt r) = show0 r

instance ShowNoQ (CTree CoInElem) where
  show0 (CTree _ _ m) = concat $ map (\(a,b) -> show a ++ ", " ++ show0 b ++ "\n") $ Map.toList $ Map.filter (isCoInTerm) m

-- Constructs a Clause tree from a list of term trees
makeCoInTree :: [TermTree] -> CoInTree
makeCoInTree ts =
  let numTerms = length ts
      domain = generateStdDomain numTerms
      treeMap = (foldl (\map (k, v) -> Map.insert k (TT v) map) Map.empty (zip domain ts))
      arityMap = (foldl (\map (k, v) -> Map.insert (TT k) v map) Map.empty (zip ts ([numTerms-1] ++ [0,0..])))
      lang = map TT ts
      rankedAlpha = (lang, arityMap)
  in  ee $ safeCTree rankedAlpha treeMap

eqCoIn :: CoInTree -> CoInTree -> Bool
eqCoIn (CTree _ d0 m0) (CTree _ d1 m1) = (sort d0) == (sort d1) && ((Map.difference m0 m1) == Map.empty)
 
--compareOnlyTT :: 

dummyXSubst = (0 :: Int ,Map.empty)

-- Saves all CoInTrees
saveCoInS :: String -> Int -> [[CoInTree]] ->  IO ()
saveCoInS _ _ [] = return ()
saveCoInS s n (ct:cts) = do
  saveCoIn (s ++ "-" ++  show n) 0 ct
  saveCoInS s (n+1) cts

-- Saves a list of CoInTrees to files
saveCoIn :: String -> Int -> [CoInTree] -> IO ()
saveCoIn _ _ [] = return ()
saveCoIn s n (ct:cts) = do
  saveFile (s ++ "-" ++ show n) ct
  saveCoIn s (n+1) cts

-- Saves all CoInTrees without the unused clauses
saveCoInS' :: String -> Int -> [[CoInTree]] ->  IO ()
saveCoInS' _ _ [] = return ()
saveCoInS' s n (ct:cts) = do
  saveCoIn' (s ++ "-" ++  show n) 0 ct
  saveCoInS' s (n+1) cts

-- Saves a list CoInTree without the unused clauses
saveCoIn' :: String -> Int -> [CoInTree] -> IO ()
saveCoIn' _ _ [] = return ()
saveCoIn' s n (ct:cts) = do
  saveMap (s ++ "-" ++ show n) (reduceMap ct)
  saveCoIn' s (n+1) cts


-- Removes all variable Strings from the CoInTree
reduceMap :: CoInTree -> Map [Int] CoInElem
reduceMap (CTree (l, a) _ m) = Map.filter (not . isCoInVariable) m


--------------------------------------------------------------------------------
------------------------------CoInTree Operations-------------------------------
--------------------------------------------------------------------------------

addTerms :: CoInTree -> [TermTree] -> [Int] -> CoInTree
addTerms ct [] _ = ct
addTerms ct (tt:tts) d = addTerms (ee $ superAddToCTree ct d (TT tt)) tts d

-- Add a substitution and variables (for unused clauses) to a CoTree
addSubst :: (Int, CoInTree) -> Int -> [Int] -> (Int, Subst) -> (Int,CoInTree)
addSubst (vc, ct) ta dd sub@(i,s) = 
  let cn = i
      varAdjusted
        | cn == 1    = addVars (vc, ee $ superAddToCTree ct dd (XSub sub)) [2..ta] dd
        | cn == ta   = (vc + (ta-1), ee $ superAddToCTree (snd $ addVars (vc, ct) [1..(ta-1)] dd) dd (XSub sub))
        | otherwise  = 
          let (nvc, ncot) = addVars (vc, ct) [1..(cn-1)] dd
          in  addVars (nvc, ee $ superAddToCTree ncot dd (XSub sub)) [(cn+1)..ta] dd
  in  varAdjusted

-- Add variables to a CoTree
addVars :: (Int,CoInTree) -> [Int] -> [Int] -> (Int,CoInTree)
addVars cotPair  []     _  = cotPair
addVars (vc,cot) (n:ns) dd 
  | checkTT (fromJust $ Map.lookup dd (mapping cot)) = (vc,cot)
  | otherwise = addVars (vc+1, addVar cot vc dd) ns dd
    where checkTT (TT tt) = isTrueTT tt
          checkTT _ = False

-- Add Variable to a CoTree
addVar :: CoInTree -> Int -> [Int] -> CoInTree
addVar ct n dd =
  let newVar = "X_" ++ show n
      --newCoT = CTree (cl ++ [(S newVar)], Map.insert (S newVar) 0 ca) cd cm
  in  ee $ superAddToCTree ct dd (S newVar)
  
-- Get all the variables in the TermTrees in the CoTree
varsCoIn :: CoInTree -> [String]
varsCoIn (CTree _ _ m) = concat $ map (varsCoInElem) $ Map.elems m

coInElemToTT :: [CoInElem] -> [TermTree]
coInElemToTT [] = []
coInElemToTT ((TT a):elems) = [a] ++ coInElemToTT elems
coInElemToTT (_:elems) = [] ++ coInElemToTT elems

fromTT :: CoInElem -> Maybe TermTree
fromTT (TT a) = Just a
fromTT _ = Nothing

fromXSub :: CoInElem -> Maybe XSubst
fromXSub (XSub a) = Just a
fromXSub _ = Nothing

-- Get the variables in a TermTree CoInElem
varsCoInElem :: CoInElem -> [String]
varsCoInElem (TT tt) = varsTerm tt
varsCoInElem _ = []

getSubstArity :: GoalTree -> [Int] -> Int
getSubstArity (CTree (_,a) _ m) d =
  let term = fromJust $ Map.lookup d m
  in  fromJust $ Map.lookup term a

-- Check if a CoTree is complete ie all leaves are either variables or True
completeCoInTree :: CoInTree -> Bool
completeCoInTree ct = 
  let leaves = findLeavesValue ct-- If all vars or complete termtree?
      filtered = filter (\x -> (not $ isCoInVariable x) && (not $ isCoInTT x)) leaves
  in  if filtered == []
      then True
      else False 

-- Check if an element of a CoTree is a Term Tree which is true
isCoInTT :: CoInElem -> Bool
isCoInTT (TT a) = isTrueTT a
isCoInTT _ = False

isCoInTerm :: CoInElem -> Bool
isCoInTerm (TT _) = True
isCoInTerm _ = False


isCoInXSub :: CoInElem -> Bool
isCoInXSub (XSub _) = True
isCoInXSub _ = False

isCoInRdt :: CoInElem -> Bool
isCoInRdt (Rdt _) = True
isCoInRdt _ = False

-- Check if an element of a CoTree is a variable
isCoInVariable :: CoInElem -> Bool
isCoInVariable (S _) = True
isCoInVariable _ = False

replaceNode :: CoInElem -> [Int] -> CoInTree -> CoInTree
replaceNode x n ct@(CTree (l,a) d m) =
  let oldVal = fromJust $ Map.lookup n m
      newMap = Map.alter (\_ -> Just x) n m
      newLang = nub $ Map.elems newMap
      newArity = Map.insert x (fromJust $ Map.lookup oldVal a) a
  in  cleanRankAlpha $ ee $ incompleteCTree (newLang, newArity) newMap
      
      

