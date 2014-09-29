module Main where

import CoALP
import CoALP.UI
import CoALP.Interpreter.Options

import Control.Arrow ((***))
import System.IO
import System.Exit
import System.Locale
import Data.Time
import Data.Maybe
import qualified Data.List as List
import qualified Data.Map as Map

data IState = IState { iProg :: Program
                     , iGoals :: [Goal]
                     , iCots :: [String]
                     , iSols :: [[Int]]
                     , iCurrent :: [Int]
                     , iNext :: [[Int]]
                     , iDTree :: DTree
                     , iQueue :: [[Int]]
                     , iTPS :: TermParserSt
                     , iDir :: [String]}

iState0 :: IState
iState0 = IState { iProg = []
                 , iGoals = []
                 , iCots = []
                 , iSols = []
                 , iCurrent = []
                 , iNext = []
                 , iDTree = empty
                 , iQueue = []
                 , iTPS = tpsInit
                 , iDir = []}

eachLine :: (Show a) => [a] -> String
eachLine [] = ""
eachLine (x:xs) = show x ++ "\n" ++ eachLine xs

promptCtrlD :: String -> IO ()
promptCtrlD thing = putStrLn $ "Please enter " ++ thing ++ " and when done type Ctrl-D on a new line."

actLoad :: IState -> IO IState
actLoad st = do
  fileName <- readLine "Type the file name and then press Enter> "
  (prg, gs, cots) <- parseItemsFile fileName
  let gcResults = guarded prg cots
  if (fst gcResults)
    then
    do drawItems (prg, gs, cots)
       return $ iState0 {iProg = prg, iGoals = gs, iCots = cots}
    else
    do putStrLn $ eachLine $ snd gcResults
       return st


actLoadFromTerminal :: IState -> String -> IO IState
actLoadFromTerminal st fileName = do
  (prg, gs, cots) <- parseItemsFile fileName
  let gcResults = guarded prg cots
  if (fst gcResults)
    then
    do drawItems (prg, gs, cots)
       return $ st {iProg = prg, iGoals = gs, iCots = cots}
    else
    do putStrLn $ eachLine $ snd gcResults
       return st

actProgram :: IState -> IO IState
actProgram st = do
  let thing = "program"
  promptCtrlD thing
  str <- readUntilEOF "> "
  --let tps0 = tpsInit {tpsNext = iNext st}
  (pr, tps) <- do
    case termParseSt onlyProgramSt (iTPS st) thing str of
      Left e  -> print e >> return (iProg st, iTPS st)
      Right r -> return r
  drawProgram pr
  let gcResults = guarded pr []
  if (fst gcResults)
    then
    do drawProgram pr
       return $ st {iProg = pr, iTPS = tps}
    else
    do putStrLn $ eachLine $ snd gcResults
       return st

actAnswer :: IState -> IO IState
actAnswer st@(IState pr g cots ss _ [] dtree q _ _) = do
  let (nextSolD, (nextQ, nextDTree)) = findNextSolutionDS prioBreadthFirst (pr, g, cots) (q, dtree)
      -- nextSol = map (getDSet nextDTree) nextSolD
      uniqueSols@(sol:sols) = cleanUpSols nextDTree nextSolD -- List.nubBy eqCoIn nextSol
      coTreeSol = coTree' $ getDSet nextDTree sol
  if nextSolD == []
    then
    do putStrLn $ "No"
       return st
    else if nextQ == [] && sols == []
           then
           do putStrLn $ (displaySolution coTreeSol g pr " - Last Solution")
              return $ st {iSols = ss ++ uniqueSols, iCurrent = sol, iNext = sols, iDTree = nextDTree, iQueue = nextQ }
           else
           do putStrLn $ (displaySolution coTreeSol g pr  " ; ")
              return $ st {iSols = ss ++ uniqueSols, iCurrent = sol, iNext = sols, iDTree = nextDTree, iQueue = nextQ}
actAnswer st@(IState pr g _ _ _ (sol:sols) dt q _ _) =
  if q == [] && sols == []
  then
  do putStrLn $ (displaySolution coTreeSol g pr " - Last Solution")
     return $ st {iCurrent = sol, iNext = sols}
  else
  do putStrLn $ (displaySolution coTreeSol g pr " ; ")
     return $ st {iCurrent = sol, iNext = sols}
  where coTreeSol = coTree' $ getDSet dt sol

cleanUpSols :: DTree -> [[Int]] -> [[Int]]
cleanUpSols dt ds =
  let dsets = map (getDSet dt) ds
  in  map fst $ List.nubBy eqDSD (zip ds dsets)

eqDSD :: ([Int],DSet) -> ([Int],DSet) -> Bool
eqDSD (_,a) (_,b) = eqDSet a b


displaySolution :: Solution -> [Goal] -> Program -> String ->  String
displaySolution (CTree _ _ m) gs pr suf =
  let sol = fromJust $ fromTT $ fromJust $ Map.lookup [1] m
      g0 = head $ head gs
      sub = fst $ ee $ termMatch g0 sol
      str = "Yes, " ++ show0 sub ++ suf
      coInRdt = Map.elems $ Map.filter (isCoInRdt) m
  in  if  coInRdt /= []
      then str ++ concat (map (showRdt pr) coInRdt)
      else str

displaySolutionFull :: Solution -> String
displaySolutionFull (CTree _ _ m) =
  let substitutions = map (show0) $ Map.elems $ Map.filter (isCoInXSub) m
  in  "Yes, " ++ (List.intercalate ", " substitutions)

actSave :: IState -> IO IState
actSave st@IState {iDTree = dtree , iCurrent = curr} = do
  fileName <- readLine "Type the file name and then press Enter> "
  t <- getCurrentTime
  let fmt = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" t
      dir = "CoALPi-" ++ fmt
      chain = getDerivationChain dtree curr
      prfx = fileName ++ "-"
      trees = map (((++) prfx) . show *** coTree') $
              zip [(1 :: Int) ..] $ reverse $ map snd chain
      reducedtrees = map (id *** reduceMap) trees
  saveDirMap dir reducedtrees
  putStrLn $ "Saved in the directory " ++ dir
  return $ st

-- (Int,[([Int], CTree String)])
showRdt :: Program -> CoInElem -> String
showRdt pr (Rdt (cn, rs)) = "\nCoinductive guard on Clause " ++ show cn ++ ": " ++ clauseTreeToString (pr !! (cn - 1)) ++
                            "\nCoinductive Guard : " ++ List.intercalate ", " (map (show0 . snd) rs)
--composition :: [Subst] -> String -> String
--composition [] s = s
--composition (sub:subs) s

--  foldM (\st' g -> do
--            let d  = derivation p m g
--                ds = d : iDer st'
--            mapM_ wr (idx $ HashSet.toList <$> d)
--            return $ st' {iDer = ds}
--        ) st gs
--  where
  -- FIXME: wr duplicates some part of the code from Dot.hs; reduce
  -- duplication by introducing a function to cover the common functionality.
--    wr (ts, i) =
--      mapM_ (\(t, j) -> do
--                putStrLn $ "GENERATION " ++ show i ++ ", TREE " ++ show j
--                putStrLn $ show t)
--            (idx ts)
--    idx :: [a] -> [(a, Int)]
--    idx l = zip l [0..]

actExit :: IState -> IO IState
actExit _ = putStrLn bye >> exitSuccess

actHelp :: IState -> IO IState
actHelp st = do
  putStrLn $ "Available commands:" ++
             "\n\tload" ++
             -- \n\tprogram\n\tgoal\n\tderivation
             "\n\tsave" ++
             -- \n\tview
             "\n\tanswer\n\texit\n\thelp"
  return st


act :: String -> IState -> IO IState
act ""           = return
act "load"       = actLoad
--act "program"    = actProgram
--act "goal"       = actGoal
--act "modes"      = actModes
--act "derivation" = actDerivation
act "save"       = actSave
--act "view"       = actView
act "answer"     = actAnswer
act "exit"       = actExit
act "help"       = actHelp
act _            = actHelp

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readLine :: String -> IO String
readLine prompt = flushStr prompt >> getLine

readUntilEOF :: String -> IO String
readUntilEOF prompt = go ""
  where
    go accum = do
      flushStr prompt
      done <- isEOF
      if done then return accum else do
        str <- getLine
        let res = accum ++ str ++ "\n"
        go res

welcome :: String
welcome =
  "░█▀▀░░░░░█▀█░█░░░█▀█░░░░▀░░█▀█░▀█▀░█▀▀░█▀▄░█▀█░█▀▄░█▀▀░▀█▀░█▀▀░█▀▄\n" ++
  "░█░░░█▀█░█▀█░█░░░█▀▀░░░░█░░█░█░░█░░█▀▀░█▀▄░█▀▀░█▀▄░█▀▀░░█░░█▀▀░█▀▄\n" ++
  "░▀▀▀░▀▀▀░▀░▀░▀▀▀░▀░░░░░░▀░░▀░▀░░▀░░▀▀▀░▀░▀░▀░░░▀░▀░▀▀▀░░▀░░▀▀▀░▀░▀\n\n" ++
  "(C) 2014, University of Dundee / Logic Group\n\n" ++
  "Type \"help\" for usage information.\n"

bye :: String
bye =
  " ______\n" ++
  "( Bye. )\n" ++
  " ------\n" ++
  "         \\   (__)\n" ++
  "          \\  (oo)\\_______\n" ++
  "             (__)\\       )\\\n" ++
  "                 ||----w |!\n" ++
  "                 ||     ||"

--nonInteractive :: CmdOptions -> IO IState
--nonInteractive op = do
--  inp <- readUntilEOF ""   -- the empty prompt
--  let (pr, gs, cots) = parseItems inp
--      st           = iState0 {iProg = pr, iGoals = gs, iCots = cots}
--      (grdLevel, grdCont) = (abs &&& (>= 0)) $ optGuards op
--      grd = all (\f -> f pr) $
--            take grdLevel [guardedClauses, guardedMatches, guardedMgus]
--  when (grdLevel /= 0 && optVerbose op > 0) $
--    putStrLn $ "Level " ++ show grdLevel ++ " guardedness check " ++
--               if grd then "PASSED." else "FAILED."
--  if grdCont && grd
--    then
--      actDerivation st >>=
--        if optView op then (actView =<<) . actSave else return
--    else
--      return st

goCoALP :: IState -> IO IState
goCoALP st = do
  cmd <- readLine "CoALP> "
  act cmd st >>= goCoALP

interactive :: IO IState
interactive = do
  putStrLn welcome
  goCoALP iState0

interactiveOptionNotValid :: IO IState
interactiveOptionNotValid = do
  putStrLn "Incorrect arguments, CoALP is initialised in interactive mode."
  putStrLn welcome
  goCoALP iState0

interactiveLoad :: String -> IO IState
interactiveLoad fileName = do
  putStrLn welcome
  st <- actLoadFromTerminal iState0 fileName
  goCoALP st

--interactiveLoadRun :: String -> IO IState
--interactiveLoadRun fileName = do
--  putStrLn welcome
--  st1 <- actLoadFromTerminal iState0 fileName
--  st2 <- actDerivation st1
--  st3 <- actAnswer st2
--  goCoALP st3

--interactiveLoadRunViewAll :: String -> IO IState
--interactiveLoadRunViewAll fileName = do
--  putStrLn welcome
--  st1 <- actLoadFromTerminal iState0 fileName
--  st2 <- actDerivation st1
--  st3 <- actSave st2
--  st4 <- actView st3
--  st5 <- actAnswer st4
--  goCoALP st5

--interactiveLoadRunView :: String -> IO IState
--interactiveLoadRunView fileName = do
--  putStrLn welcome
--  st1 <- actLoadFromTerminal iState0 fileName
--  st2 <- actDerivation st1
--  st3 <- actSaveFinal st2
--  st4 <- actView st3
--  st5 <- actAnswer st4
--  goCoALP st5

-- | Command-line option dispatcher.
--
-- FIXME: Values of options should really be kept in the state and referred to
-- during program actions rather than being forgotten after firing off only once
-- at the start of the program. Values of options should be available for
-- reading and updating during the interactive session.
goOptions :: CmdOptions -> IO IState
goOptions op
--  | optStdin op = nonInteractive op
  | optLoad op == "" = interactive
  | not (optRun op) && not (optView op) = interactiveLoad $ optLoad op
--  | optRun op && not (optView op) = interactiveLoadRun $ optLoad op
--  | optRun op && optView op && (optGraphics op == "all") =
--    interactiveLoadRunViewAll $ optLoad op
--  | optRun op && optView op && (optGraphics op == "final") =
--      interactiveLoadRunView $ optLoad op
goOptions _ = interactiveOptionNotValid

main :: IO IState
main =  parseOptions >>= goOptions
