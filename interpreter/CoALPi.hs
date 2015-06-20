module Main where

import CoALP
import CoALP.UI
import CoALP.Interpreter.Options

import System.IO
import System.Exit
import Data.Time
import System.Locale
import System.Process
import Control.Exception
import Control.Monad
import Control.Applicative ( (<$>) )
import Control.Arrow
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Lazy as HashMap

-- | Type of interpreter state.
data IState = IState
              {
                iProg  :: Program1                -- ^ logic clauses
              , iGoal  :: Goal1                   -- ^ goal
              , iNext  :: Int                     -- ^ the next variable
              , iDer   :: [[HashSet (ONode Occ)]] -- ^ derivations, one per each
                                                  -- goal
              , iDir   :: [String]                -- ^ saved derivation
                                                  -- directories, one per each
                                                  -- derivation
              }

-- | The initial state.
iState0 :: IState
iState0 = IState (Pr []) [] (ModeAssoc HashMap.empty) 0 [] []

promptCtrlD :: String -> IO ()
promptCtrlD thing =
  putStrLn $ "Type in your " ++ thing ++
             " and finish by typing Ctrl-D on a new line."

actLoad :: IState -> IO IState
actLoad st = do
  fileName <- readLine "Type the file name and then press Enter> "
  (cs, gs, ms) <- parseItemsFile fileName
  let pr = Pr cs
      m = unionModeAssoc ms
  if guarded pr
    then
    do putStrLn $ "\n" ++ show cs ++ "\n" ++ show gs ++ "\n" ++ show m
       return $ st {iProg = pr, iGoals = gs, iModes = m, iNext = 0}
    else
    do putStrLn $ "The given program is unguarded\n"
       return st
    -- FIXME: 1) Retrieve the next variable from the parser state or disallow
    -- separate changes to the program or goals. The latter is more preferable.
    -- 2) Allow for multiple goals in the interpreter state.

actLoadFromTerminal :: IState -> String -> IO IState
actLoadFromTerminal st fileName = do
  (cs, gs, ms) <- parseItemsFile fileName
  let pr = Pr cs
      m = unionModeAssoc ms
  if guarded pr
    then
    do putStrLn $ "\n" ++ show cs ++ "\n" ++ show gs ++ "\n" ++ show m
       return $ st {iProg = pr, iGoals = gs, iModes = m, iNext = 0}
    else
    do putStrLn $ "The given program is unguarded\n"
       return st

actProgram :: IState -> IO IState
actProgram st = do
  let thing = "program"
  promptCtrlD thing
  str <- readUntilEOF "> "
  let tps0 = tpsInit {tpsNext = iNext st}
  (pr, tps) <- do
    case termParseSt onlyProgramSt tps0 thing str of
      Left e  -> print e >> return (iProg st, tps0)
      Right r -> return r
  putStrLn $ "\n" ++ show pr
  if guarded pr
    then
    do return $ st {iProg = pr, iNext = tpsNext tps}
    else
    do putStrLn $ "\nThe given program is unguarded\n"
       return st

actGoal :: IState -> IO IState
actGoal st = do
  let thing = "goal"
  promptCtrlD thing
  str <- readUntilEOF "> "
  let tps0 = tpsInit {tpsNext = iNext st}
  (gs, tps) <- do
    case termParseSt onlyGoalSt tps0 thing str of
      Left e  -> print e >> return (iGoals st, tps0)
      Right (g, tps) -> return ([g], tps)
  putStrLn $ "\n" ++ show gs
  return $ st {iGoals = gs, iNext = tpsNext tps}

actModes :: IState -> IO IState
actModes st = do
  let thing = "modes"
  promptCtrlD thing
  str <- readUntilEOF "> "
  ms <- do
    case termParse onlyModeAssocs thing str of
      Left e  -> print e >> return (iModes st)
      Right r -> return r
  putStrLn $ "\n" ++ show ms
  return $ st {iModes = ms}

actDerivation :: IState -> IO IState
actDerivation st@IState{iProg = p, iModes = m, iGoals = gs} = do
  foldM (\st' g -> do
            let d  = derivation p m g
                ds = d : iDer st'
            mapM_ wr (idx $ HashSet.toList <$> d)
            return $ st' {iDer = ds}
        ) st gs
  where
    -- FIXME: wr duplicates some part of the code from Dot.hs; reduce
    -- duplication by introducing a function to cover the common functionality.
    wr (ts, i) =
      mapM_ (\(t, j) -> do
                putStrLn $ "GENERATION " ++ show i ++ ", TREE " ++ show j
                putStrLn $ show t)
            (idx ts)
    idx :: [a] -> [(a, Int)]
    idx l = zip l [0..]

actSave :: IState -> IO IState
actSave st = do
  t <- getCurrentTime
  dirs <-
    forM (iDer st) $ \d -> do
      let fmt = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" t
          dir = "CoALPi-" ++ fmt
      save dir d
      putStrLn $ "Saved in the directory " ++ dir
      return dir
  return $ st {iDir = dirs}

actSaveFinal :: IState -> IO IState
actSaveFinal st = do
  t <- getCurrentTime
  dirs <-
    forM (iDer st) $ \d -> do
      let fmt = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" t
          dir = "CoALPi-" ++ fmt
      saveFinal dir d
      putStrLn $ "Saved in the directory " ++ dir
      return dir
  return $ st {iDir = dirs}

actView :: IState -> IO IState
actView st
  | iDir st == [] = do
    putStrLn "Nothing to view. Save a derivation first."
    return st
  | otherwise = do
    let cmd = "sleep 1; eog " ++ concatMap (++ "/*.png ") (iDir st)
    (void $ runCommand cmd) `catch` (print :: SomeException -> IO ())
    return st

actAnswer :: IState -> IO IState
actAnswer st
  | iDer st == [] = do
    putStrLn "Execute a derivation first."
    return st
  | otherwise = do
    putStrLn "Goals: "
    print (iGoals st)
    putStrLn "Answer:"
    _ <-
      forM (iDer st) $ \d -> do
        print (rootTree $ head $ last $ HashSet.toList <$> d)
    return st

actExit :: IState -> IO IState
actExit _ = putStrLn bye >> exitSuccess

actHelp :: IState -> IO IState
actHelp st = do
  putStrLn $ "Available commands:" ++
             "\n\tload\n\tprogram\n\tgoal\n\tderivation\n\tsave\n\tview" ++
             "\n\tanswer\n\texit\n\thelp"
  return st

act :: String -> IState -> IO IState
act ""           = return
act "load"       = actLoad
act "program"    = actProgram
act "goal"       = actGoal
act "modes"      = actModes
act "derivation" = actDerivation
act "save"       = actSave
act "view"       = actView
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
  "(C) 2014-2015, University of Dundee / Logic Group\n\n" ++
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

nonInteractive :: CmdOptions -> IO IState
nonInteractive op = do
  inp <- readUntilEOF ""   -- the empty prompt
  let (cs, gs, ms) = parseItems inp
      pr           = Pr cs
      m            = unionModeAssoc ms
      st           = iState0 {iProg = pr, iGoals = gs, iModes = m}
      (grdLevel, grdCont) = (abs &&& (>= 0)) $ optGuards op
      grd = all (\f -> f pr) $
            take grdLevel [const True {-FIXME-}, guardedMatches, undefined]
  when (grdLevel /= 0 && optVerbose op > 0) $
    putStrLn $ "Level " ++ show grdLevel ++ " guardedness check " ++
               if grd then "PASSED." else "FAILED."
  if grdCont && grd
    then
      actDerivation st >>=
        if optView op then (actView =<<) . actSave else return
    else
      return st

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

interactiveLoadRun :: String -> IO IState
interactiveLoadRun fileName = do
  putStrLn welcome
  st1 <- actLoadFromTerminal iState0 fileName
  st2 <- actDerivation st1
  st3 <- actAnswer st2
  goCoALP st3

interactiveLoadRunViewAll :: String -> IO IState
interactiveLoadRunViewAll fileName = do
  putStrLn welcome
  st1 <- actLoadFromTerminal iState0 fileName
  st2 <- actDerivation st1
  st3 <- actSave st2
  st4 <- actView st3
  st5 <- actAnswer st4
  goCoALP st5

interactiveLoadRunView :: String -> IO IState
interactiveLoadRunView fileName = do
  putStrLn welcome
  st1 <- actLoadFromTerminal iState0 fileName
  st2 <- actDerivation st1
  st3 <- actSaveFinal st2
  st4 <- actView st3
  st5 <- actAnswer st4
  goCoALP st5

-- | Command-line option dispatcher.
--
-- FIXME: Values of options should really be kept in the state and referred to
-- during program actions rather than being forgotten after firing off only once
-- at the start of the program. Values of options should be available for
-- reading and updating during the interactive session.
goOptions :: CmdOptions -> IO IState
goOptions op
  | optStdin op = nonInteractive op
  | optLoad op == "" = interactive
  | not (optRun op) && not (optView op) = interactiveLoad $ optLoad op
  | optRun op && not (optView op) = interactiveLoadRun $ optLoad op
  | optRun op && optView op && (optGraphics op == "all") =
    interactiveLoadRunViewAll $ optLoad op
  | optRun op && optView op && (optGraphics op == "final") =
      interactiveLoadRunView $ optLoad op
goOptions _ = interactiveOptionNotValid

main :: IO IState
main =  parseOptions >>= goOptions
