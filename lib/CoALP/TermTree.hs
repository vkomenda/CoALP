{-# LANGUAGE TypeOperators #-}

-- 18/07/2014
-- Reorganised Modules

module CoALP.TermTree where

import Data.Maybe
import Data.Char
import Data.List
import           Data.Map (Map)
import qualified Data.Map as Map

import CoALP.CTree

type TermTree = CTree String

-- Term Tree representing when a statement is true
trueTT :: TermTree
trueTT = makeTermTree (Map.insert [] "◻" Map.empty) 

-- Checks if a termtree is the symbol for true
isTrueTT :: TermTree -> Bool
isTrueTT (CTree _ d m) =
  if length d == 1 && Map.elems m == ["◻"]
  then True
  else False


-- Converts a map into a CTree (calculates arity based on the map itself)
makeTermTree :: Map.Map [Int] String -> TermTree
makeTermTree m = 
  let domain = Map.keys m
      language = Map.elems m
      calcArity = map (flip countChildren m) domain
      arityMap = (foldl (\map (k, v) -> Map.insert k v map) Map.empty (zip language calcArity))
      rankedAlpha = (language, arityMap)
  in  ee $ safeCTree rankedAlpha m

--------------------------------------------------------------------------------
-----------------------------Term Tree Operations-------------------------------
--------------------------------------------------------------------------------
 
-- Gets all variables in a rankedAlpha
varsRanked :: TermTree -> [String]
varsRanked (CTree (l,_) _ _) = filter (startWithUpper) l
  where startWithUpper (x:xs) = isUpper x

varsTerm :: TermTree -> [String]
varsTerm (CTree _ _ m) = nub $ filter (startWithUpper) (Map.elems m)
  where startWithUpper (x:xs) = isUpper x

-- Get all domains of variables in a TermTree paired with their name
varsDom :: TermTree -> [(String, [[Int]])]
varsDom t@(CTree _ _ tm) =
  let variables = varsTerm t
      domains = map (flip findValueDomains t) variables
  in  zip variables domains

mergeTTRA :: [TermTree] -> RankedAlphabet String
mergeTTRA tts = mergeRankAlpha $ map (rankedAlpha) tts

replaceTTreeRA :: [TermTree] -> RankedAlphabet String -> [TermTree]
replaceTTreeRA tts ra = map (flip replaceRA ra) tts

tHead :: TermTree -> String
tHead = fromJust . Map.lookup [] . mapping

--------------------------------------------------------------------------------
-------------------------------Displaying Term Tree-----------------------------
--------------------------------------------------------------------------------

-- Displays the TermTree as a term
drawTerms :: TermTree -> IO ()
drawTerms = putStrLn . termTreeToString

-- Converts a TermTree into a Term
termTreeToString :: TermTree -> String
termTreeToString t = convertToTerm (mapping t) []

-- Converts a maping and node into a Term
convertToTerm :: ([Int] --> String) -> [Int] -> String
convertToTerm m c
  | hasChild c m = (fromJust $ Map.lookup c m) ++ "(" ++ (commaSep $ map (convertToTerm m) (findChildren c m)) ++ ")"
  | otherwise    = (fromJust $ Map.lookup c m)	

-- Seperates each string with a comma
commaSep :: [String] -> String
commaSep [] = ""
commaSep (x:[]) = x 
commaSep (x:xs) = x ++ "," ++ commaSep xs


