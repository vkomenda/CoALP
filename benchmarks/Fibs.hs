{-# LANGUAGE BangPatterns #-}

import CoALP
import CoALP.UI

import Control.Applicative ( (<$>) )
import Control.DeepSeq
import Control.Monad
import Data.List (intercalate)
import Data.Time.Clock
import qualified Data.HashSet as Set

fibP :: String
fibP = "add (0, Y, Y).\n" ++
       "add (s (X), Y, s (Z)) :- add (X, Y, Z).\n" ++
       "fibs (X, Y, cons (X, S)) :- add (X, Y, Z), fibs (Y, Z, S).\n" ++
       "nth (0, cons (X, S), X).\n" ++
       "nth (s (N), cons (X, S), Y) :- nth (N, S, Y).\n" ++
       "fib (N, X) :- fibs (0, s (0), S), nth (N, S, X).\n"

nat :: Int -> String
nat n | n == 0 = "0"
      | n >  0 = "s (" ++ nat (n-1) ++ ")"
      | otherwise = error $ "nat of " ++ show n ++ " is not defined"

--fibnP :: Int -> String
--fibnP n = fibP ++ "(fib" ++ show n ++ " X) :- (fib " ++ nat n ++ " X)."

mods :: ModeAssoc
mods = modeAssocsFromString $
    "add  (+!, +!, -!) " ++
    "add  (+!, -!, -!) " ++
    "fibs (+!, +!, -?) " ++
    "fibs (+!, -!, -?) " ++
    "fibs (-!, -!, -?) " ++
    "nth  (+!, -?, -!) " ++
    "fib  (+!, -!) "

fibnG :: Int -> String
fibnG n = ":- fib (" ++ nat n ++ ", X)."

main :: IO ()
main = do
  print p
  print mods

  forM_ [1..maxFib] $ \i -> do
    putStrLn $ "Running the fib " ++ show i ++ " benchmark..."
    benchmark i $ "fib" ++ show i
    putStrLn $ take 80 $ repeat '='

maxFib :: Int
maxFib = 10

noMoreGenerations :: Int
noMoreGenerations = 10000

p   :: Program1
tps :: TermParserSt
(p, tps) = fromStringSt onlyProgramSt tpsInit fibP

benchmark :: Int -> String -> IO ()
benchmark n dir = do
  let g = fst $ fromStringSt onlyGoalSt tps (fibnG n)
  print p
  print mods
  print g
  start0 <- getCurrentTime
  let !d = force $ take noMoreGenerations $ derivation p mods g
  end0 <- getCurrentTime
  putStrLn $ "Time: " ++ show (diffUTCTime end0 start0)
  let lastgen = length d - 1
      lens = Set.size <$> d
      fin  = Set.filter finalONode <$> d
  putStrLn $ "Total derivation steps (of expansion by mgu): " ++
             show lastgen
  putStrLn $ "Trees in each generation: " ++
             foldl1 (\s -> (++) (s ++ ", ")) (show <$> lens)
  putStrLn $ "Total trees: " ++ (show $ sum lens)
  putStrLn $ "Final trees: " ++ show (sum $ Set.size <$> fin)
  putStrLn $ "Variables in final trees: " ++
             (intercalate ", " . map show . concat)
             (map (map varsONode . Set.toList) fin)
  save dir fin
