{-# LANGUAGE TypeOperators #-}

module CoALP.UI.Dot where

import CoALP.CTree
import CoALP.UI.Printer

import Data.List
import Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
import System.Process
import System.Directory
import Control.Exception
import Control.Monad (void)


--------------------------------------------------------------------------------
-------------------------------Graphviz for CTree-------------------------------
--------------------------------------------------------------------------------

-- Outputs the tree as a string in ImageMagick dot format.
gVizCTree :: (ShowNoQ  a) => CTree a -> IO ()
gVizCTree = putStrLn . render

-- | Renders a tree as a string in the ImageMagick dot format.
render :: (ShowNoQ  a) => CTree a -> String
render t = "digraph G {\n" ++ concat (map (thd3) $ numberDomain (sort $ domain t) (mapping t)) ++ "}"

-- Get the third element of a 3-Tuple
thd3 :: (a,b,c) -> c
thd3 (a,b,c) = c

-- Creates a list of (Domain, ID, ImageMagic String) from a Domain and a mapping
numberDomain :: (ShowNoQ  a) => Domain -> ([Int] --> a) -> [([Int], Int, String)]
numberDomain d m = connectUp $ numberAdjustment 0 0 1 (zip (lsort d) [1,2..]) m

-- Inserts points and connectors into the list
-- Accumulator is the number of previous points to be added, l is the current level of the tree, s is the size of the current level of the tree (perhaps more the offset for any points which need to be created, starts off as the size of he current level of the tree).
-- xs is the domains paired with IDs, m is the mapping for the tree
numberAdjustment :: (ShowNoQ a) => Int -> Int -> Int -> [([Int], Int)] -> ([Int] --> a) -> [([Int], Int, String)]
numberAdjustment _ _ _ [] _ = []
numberAdjustment acc level s xs@((a,b):ds) m
  -- when its the Root node
  | acc == 0 && level == 0 = label ++ numberAdjustment 1 0 levelSize ds m -- ++ connector ++ [([],1, newConnector 0 1)]
  -- When a new level is reached calculate the size of the level and adjust the IDs using adjustLevel
  | (length a) /= level    = numberAdjustment acc (level+1) levelSize (adjustLevel (level+1) acc xs) m
  -- Check if node has a child. When it does create a new label, and point, move to the next in the list and finally add a connector
  | (hasChild a m)     = label ++ numberAdjustment (acc + 1) level s ds m -- ++ connector
  -- Otherwise just add a new label and then move onto the next in the list
  | otherwise          = label ++ numberAdjustment acc level (s-1) ds m
    where label     = [(a, b, newLabel b $ fromJust $ Map.lookup a m)]
          --point     = [(a, b+s, newPoint $ b+s)]
          --connector = [(a, b+s, newConnector b $ b+s)]
          levelSize = (length $ getLevel (level+1) $ map (fst) xs)

-- Increment the IDs by the value of the accumulator
adjustLevel :: Int -> Int -> [([Int], Int)] -> [([Int], Int)]
adjustLevel _ _ [] = []
adjustLevel l acc xs@((a,b):ds) =
  if (length a) == l
  then [(a, b + acc)] ++ adjustLevel l acc ds
  else xs

-- Gets all the nodes on a level of the tree
getLevel :: Int -> Domain -> Domain
getLevel l d = filter (checkSize l) d
  where
    checkSize l x =
      if (length x) == l
      then True
      else False

-- Connects the points with their appropriate children
connectUp :: [([Int], Int, String)] -> [([Int], Int, String)]
connectUp x = x ++ addConnections (getLabels x) (getLabels x)

-- Returns the list of connections between points and their children
addConnections :: [([Int], Int, String)] -> [([Int], Int, String)] -> [([Int], Int, String)]
addConnections [] _ = []
addConnections (x:xs) ys = connect x (filter (isChild x) ys) ++ addConnections xs ys
  where connect :: ([Int], Int, String) -> [([Int], Int, String)] -> [([Int], Int, String)]
        connect _ [] = []
        connect x@(l, a, _) ((_, b, _):ys) = [(l, 0, newConnector a b)] ++ connect x ys

-- Checks if b is the child of a
isChild :: ([Int], Int, String) -> ([Int], Int, String) -> Bool
isChild (a, _, _) (b, _, _) =
  if (a `isPrefixOf` b) && ((length a) == (length b)-1)
  then True
  else False

-- gets all the points
getPoints :: [([Int], Int, String)] -> [([Int], Int, String)]
getPoints xs = filter (isPoint) xs
  where isPoint (a,b,c) = " [shape=point];\n" `isSuffixOf` c

-- Gets all the labels
getLabels :: [([Int], Int, String)] -> [([Int], Int, String)]
getLabels xs = filter (isLabel) xs
  where isLabel (a,b,c) = " [shape=none,label=" `isInfixOf` c

-- Creates a new point
newPoint :: Int -> String
newPoint x = show x ++ " [shape=point];\n"

-- Creates a new connector
newConnector :: Int -> Int -> String
newConnector x y = show x ++ " -> " ++ show y ++ " [arrowhead=none];\n"

-- Creates a new label
newLabel :: (ShowNoQ  a) => Int -> a -> String
newLabel x a = show x ++ " [shape=none,label=\"" ++ show0 a ++ "\"];\n"

--------------------------------------------------------------------------------
---------------------------------Write to File----------------------------------
--------------------------------------------------------------------------------

-- Saves a map to the file named and daws it in a png
saveMap :: (ShowNoQ a) => String -> Map [Int] a -> IO ()
saveMap base m = do
  writeFile (base ++ ".gv") ("digraph G {\n" ++ concat (map (thd3) $ numberDomain (sort $ (Map.keys m)) m) ++ "}")
  void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++ base ++ ".png"

-- Saves a tree to the file named and draws it in a png
saveFile :: (ShowNoQ a) => String -> CTree a -> IO ()
saveFile base t = do
  writeFile (base ++ ".gv") (render t)
  void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++ base ++ ".png"

-- Saves a List of tree to a driectory with the prefix given
saveDirTree :: (ShowNoQ a) => String -> [(String, CTree a)] -> IO ()
saveDirTree dir ts =
  flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    mapM_ (\(a,b) -> saveFile (dir ++ "/" ++ a) b) ts

-- Saves a List of tree to a driectory with the prefix given
saveDirMap :: (ShowNoQ a) => String -> [(String, Map [Int] a )] -> IO ()
saveDirMap dir ms =
  flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    mapM_ (\(a,b) -> saveMap (dir ++ "/" ++ a) b) ms

-- Saves a list of tress to the directory named and draws them as pngs
saveDir :: (ShowNoQ a) => String -> [CTree a] -> IO ()
saveDir dir ts =
  flip catch (print :: IOError -> IO ()) $ do
    let indexed = idx ts
    createDirectory dir
    mapM_ (wr) indexed
  where
    wr (t, n) = do
      let base = dir ++ "/" ++ show n
      writeFile (base ++ ".gv") (render t)
      void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++ base ++ ".png"
    idx :: [a] -> [(a, Int)]
    idx l = zip l [0..]
