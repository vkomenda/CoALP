
-- 30/07/2014
-- Added substitution tree

module CoALP.Substitution where

import Data.Maybe
import Data.Char
import Control.Monad.State.Lazy
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Foldable
import qualified Data.Foldable as Fold

import CoALP.CTree
import CoALP.TermTree
import CoALP.ClauseTree
import CoALP.UI.Parser

type Subst = Map String TermTree
type SubstTree = CTree (Int, Subst)

unify :: TermTree -> TermTree -> Either String (Subst, TermTree)
unify t0 t1 = mguTerm t0 t1 [] Map.empty

termMatch :: TermTree -> TermTree -> Either String (Subst, TermTree)
termMatch t0 t1 = matchTerm t0 t1 [] Map.empty

termMatch' :: TermTree -> TermTree -> Either String (Subst, TermTree)
termMatch' t0 t1 = matchTerm' t0 t1 [] Map.empty

termMatchSwapped :: TermTree -> TermTree -> Either String (Subst, TermTree)
termMatchSwapped t1 t0 = matchTerm t0 t1 [] Map.empty

-- Most general unifier
mguTerm :: TermTree -> TermTree -> [Int] -> Subst -> Either String (Subst, TermTree)
mguTerm t0@(CTree _ _ m0) t1@(CTree _ _ m1) cd sm 
  | isVariable curr0 && curr0 == curr1 = Right (sm, t0)
  | isVariable curr0 && curr0 `Fold.notElem` replacement = chainTermMatch mguTerm replacedTree t1 cd (Right newSubst) 
  | isVariable curr0 = Left ("Occurs check failed at domain " ++ show cd ++ " \n\"" ++ curr0 ++ "\" was found within \"" ++ (show replacement) ++ "\"")
  | isVariable curr1 && not (isVariable curr0) = mguTerm t1 t0 cd sm
  | curr0 /= curr1 = Left ("Ident Mismatch \n\"" ++ curr0 ++ "\" does not match \"" ++ curr1 ++ "\"")
  | otherwise = chainTermMatch mguTerm t0 t1 cd (Right sm)
  where curr0 = fromJust $ Map.lookup cd m0
        curr1 = fromJust $ Map.lookup cd m1
        replacement = ee $ getSubCTree t1 cd
        replacedTree = replaceVars t0 t1 cd
        newSubst = Map.insert curr0 replacement sm

-- Merges substitutions
mergeSubst :: String -> TermTree -> Subst -> Either String Subst
mergeSubst s1 s2 sm
  | mappedTo == Nothing = Right (Map.insert s1 s2 sm)
  | mappedTo == Just s2 = Right sm
  | otherwise = Left ("\"" ++ s1 ++ "\" was already assigned to \"" ++ show (fromJust (mappedTo)) ++ "\" cannot now be assigned to \"" ++ (show s2) ++ "\"")
  where mappedTo = Map.lookup s1 sm

-- Term Matching
matchTerm :: TermTree -> TermTree -> [Int] -> Subst -> Either String (Subst, TermTree)
matchTerm t0@(CTree _ _ m0) t1@(CTree _ _ m1) cd sm
  | isVariable curr0 && curr0 `Fold.notElem` replacement = chainTermMatch matchTerm t0 t1 cd (mergeSubst curr0 replacement sm)
  | isVariable curr0 = Left ("Occurs check failed at domain " ++ show cd ++ " \n\"" ++ curr0 ++ "\" was found within \"" ++ (show replacement) ++ "\"")
  | curr0 /= curr1 = Left ("Ident Mismatch \n\"" ++ curr0 ++ "\" does not match \"" ++ curr1 ++ "\"")
  | otherwise = chainTermMatch matchTerm t0 t1 cd (Right sm)
  where curr0 = fromJust $ Map.lookup cd m0
        curr1 = fromJust $ Map.lookup cd m1
        replacement = ee $ getSubCTree t1 cd

matchTerm' :: TermTree -> TermTree -> [Int] -> Subst -> Either String (Subst, TermTree)
matchTerm' t0@(CTree _ _ m0) t1@(CTree _ _ m1) cd sm
  | isVariable curr0 = chainTermMatch matchTerm' t0 t1 cd (mergeSubst curr0 replacement sm)
  -- | isVariable curr0 = Left ("Occurs check failed at domain " ++ show cd ++ " \n\"" ++ curr0 ++ "\" was found within \"" ++ (show replacement) ++ "\"")
  | curr0 /= curr1 = Left ("Ident Mismatch \n\"" ++ curr0 ++ "\" does not match \"" ++ curr1 ++ "\"")
  | otherwise = chainTermMatch matchTerm' t0 t1 cd (Right sm)
  where curr0 = fromJust $ Map.lookup cd m0
        curr1 = fromJust $ Map.lookup cd m1
        replacement = ee $ getSubCTree t1 cd


-- Adjusts the current domain based on what is in the tree
chainTermMatch :: (TermTree -> TermTree -> [Int] -> Subst -> Either String (Subst, TermTree)) ->
                  TermTree -> TermTree -> [Int] -> Either String Subst ->  Either String (Subst, TermTree)
chainTermMatch f t0 t1 cd (Left sm) = Left sm
chainTermMatch f t0 t1 cd (Right sm)
  | hasChild cd (mapping t0) && hasNeighbour cd t0 = 
    case substChild of
      Right newSM -> f (snd newSM) t1 (neighbour cd) (fst newSM) 
      Left _ -> substChild
  | hasChild cd (mapping t0) = f t0 t1 (cd ++ [1]) sm 
  | hasNeighbour cd t0 = f t0 t1 (neighbour cd) sm 
  | otherwise = Right (sm, t0)
  where substChild = f t0 t1 (cd ++ [1]) sm


-- Replaces the appropriate variable in the first tree based on the value at the domain in the 2nd tree
replaceVars :: TermTree -> TermTree -> [Int] -> TermTree
replaceVars t0@(CTree _ _ m0) t1 cd =
  let toReplace = findValueDomains (fromJust $ Map.lookup cd m0) t0
      replacement = ee $ getSubCTree t1 cd
  in  replaceNodesAt replacement t0 toReplace

substitute :: TermTree -> Subst -> TermTree
substitute t sm =
  let toSubstitute = Map.keys sm
      toReplace = map (flip findValueDomains t) toSubstitute
      subs = map (fromJust . flip Map.lookup sm) toSubstitute 
      paired = zip toReplace subs
      applySubs (x:xs) t0 = applySubs xs (replaceNodesAt (snd x) t0 (fst x))
      applySubs [] t0 = t0
  in  applySubs paired t


-- Check if is a variable
isVariable :: String -> Bool
isVariable (x:xs) = isUpper x

-- Given a list of subst and a clause number return all the substs using that clause
getClauseSubst :: [(Int,Subst)] -> Int -> [(Int,Subst)]
getClauseSubst subs cn = filter (\(a,b) -> a == cn) subs

clauseRepeated ::  [(Int,Subst)] -> Int -> Bool
clauseRepeated subs cn = 
  if length (getClauseSubst subs cn) <= 1
  then False
  else True


substToString :: Map String TermTree -> String
substToString m = 
  let kv = Map.toList m
      subs = map (\(k,v) -> k ++ " -> " ++ (convertToFnString [[]] v)) kv
  in  if subs == []
      then ""
      else Prelude.concat $ ((map (++ ", ") (init subs)) ++ [last subs])

--isNotContained :: String -> TermTree -> Bool

