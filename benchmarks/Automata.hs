{-# LANGUAGE BangPatterns #-}

import CoALP
import CoALP.UI

import Control.Applicative ( (<$>) )
import Control.DeepSeq
import Data.List (intercalate)
import Data.Time.Clock
import qualified Data.HashSet as Set

automatonP :: String
automatonP =
  "(automaton (cons X T) St) :- (trans St X NewSt), (automaton T NewSt). " ++
  "(automaton nil St) :- (final St). " ++
  "(trans s0 a s1) :- . " ++
  "(trans s2 c s3) :- . " ++
  "(trans s2 e s0) :- . " ++
  "(trans s1 b s2) :- . " ++
  "(trans s3 d s0) :- . " ++
  "(final s2) :- . "

automatonG :: String
automatonG = ":- (automaton X s0)."

mods :: ModeAssoc
mods = modeAssocsFromString $
  "automaton -! +!. " ++
  "automaton -! -!. " ++
  "trans +! +! -!. " ++
  "trans +! -! -!. " ++
  "trans -! -! -!. " ++
  "final -!. "

main :: IO ()
main = benchmark

noMoreGenerations :: Int
noMoreGenerations = 10000

benchmark :: IO ()
benchmark = do
  let (p, tps) = fromStringSt onlyProgramSt tpsInit automatonP
      (g, _) = fromStringSt onlyGoalSt tps automatonG
      m = mods
  print p
  print m
  print g
  start0 <- getCurrentTime
  let !d = force $ take noMoreGenerations $ derivation p m g
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
  save "automata" fin
