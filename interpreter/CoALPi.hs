module Main where

import CoALP
import CoALP.UI
import CoALP.Interpreter.Options

import System.IO
import System.Exit
import qualified Data.Array as Array
import Data.Maybe
import Data.Time
import System.Locale
import System.Process
import Control.Exception
import Control.Monad
--import Control.Applicative ( (<$>) )
import Control.Arrow

-- | Type of interpreter state.
data IState = IState
              {
                iProg  :: Maybe Program1          -- ^ logic clauses
              , iGoals :: [Goal1]                 -- ^ goals
              , iNext  :: Int                     -- ^ the next variable
              , iDer   :: Maybe (Derivation TreeOper1 Transition TreeOper1)
                          -- ^ derivation
              , iDerCI :: Maybe (Derivation TreeOper1 TransGuards [Term1Loop])
                          -- ^ derivation with coinductive invariants
              , iDir   :: String                  -- ^ save directory
              }

-- | The initial state.
iState0 :: IState
iState0 = IState Nothing [] 0 Nothing Nothing ""

promptCtrlD :: String -> IO ()
promptCtrlD thing =
  putStrLn $ "Type in your " ++ thing ++
             " and finish by typing Ctrl-D on a new line."

actLoad :: IState -> IO IState
actLoad st = do
  fileName <- readLine "Type the file name and then press Enter> "
  (cs, gs) <- parseItemsFile fileName
  let pr = Program $ Array.listArray (0, length cs - 1) cs
      uLoops = matchLoops pr
  if null uLoops
    then
    do putStrLn $ "\n" ++ show cs ++ "\n" ++ show gs
       return $ st {iProg = Just pr, iGoals = gs}
    else
    do putStrLn $ show3Loops uLoops
       return st
    -- TODO? 1) Retrieve the next variable from the parser state or disallow
    -- separate changes to the program or goals. The latter is more preferable.
    -- 2) Allow for multiple goals in the interpreter state.

actLoadFromTerminal :: CmdOptions -> IState -> IO IState
actLoadFromTerminal op st = do
  (cs, gs) <- parseItemsFile $ optLoad op
  let pr = Program $ Array.listArray (0, length cs - 1) cs
      (grdLevel, grdCont) = ((max 1 . min 3 . abs) &&& (>= 0)) $ optGuards op
      uLoops = [[], matchLoops pr, resolutionLoops pr]!!(grdLevel - 1)
  if null uLoops
    then
    do putStrLn $ "\n" ++ show cs ++ "\n" ++ show gs
       return $ st {iProg = Just pr, iGoals = gs}
    else
    do putStrLn $ show3Loops uLoops
       return st

show3Loops :: [Term1Loop] -> String
show3Loops loops = "Program admits loops " ++ show (take 3 loops) ++ "\n"

actProgram :: IState -> IO IState
actProgram st = do
  let thing = "program"
  promptCtrlD thing
  str <- readUntilEOF "> "
  let tps0 = tpsInit {tpsNext = iNext st}
  (pr, tps) <- do
    case termParseSt onlyProgramSt tps0 thing str of
      Left e  -> print e >> return (iProg st, tps0)
      Right (p, s) -> return (Just p, s)
  putStrLn $ "\n" ++ show pr
  if isJust pr
    then do
      let uLoops = resolutionLoops (fromJust pr)
      if null uLoops
        then return $ st {iProg = pr, iNext = tpsNext tps}
        else do
          putStrLn $ "\n" ++ show3Loops uLoops
          return st
    else return st

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

actSearch :: IState -> IO IState
actSearch st@IState{iProg = Nothing} = do
  putStrLn "There is no program"
  return st
actSearch st@IState{iGoals = []} = do
  putStrLn "There is no goal"
  return st
actSearch st@IState{iDer = Just d} = do
  let (r1, d1) = continueResolution d
  putStrLn $ show r1
  return $ st {iDer = Just d1}
actSearch st@IState{iProg = Just p, iGoals = g:_} = do
  let (r, d) = runResolution p g
  putStrLn $ show r  -- FIXME: pretty print
  return $ st {iDer = Just d}

actCheck :: IState -> IO IState
actCheck st@IState{iProg = Nothing} = do
  putStrLn "There is no program"
  return st
actCheck st@IState{iGoals = []} = do
  putStrLn "There is no goal"
  return st
actCheck st@IState{iDerCI = Just d} = do
  let (r1, d1) = continueGuards d
  putStrLn $ show r1
  return $ st {iDerCI = Just d1}
actCheck st@IState{iProg = Just p, iGoals = g:_} = do
  let (r, d) = runGuards p $ goalTree (Array.bounds $ program p) g
  putStrLn $ show r  -- FIXME: pretty print
  return $ st {iDerCI = Just d}

actSave :: IState -> IO IState
actSave st@IState{iDer = Nothing, iDerCI = Nothing} = do
  putStrLn "Nothing to save"
  return st
actSave st = do
  t <- getCurrentTime
  let fmt = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" t
      dir = "CoALPi-" ++ fmt
  when (isJust $ iDer st) $ do
    let d = fromJust $ iDer st
    save dir d
    putStrLn $ "Derivation saved in " ++ dir
  when (isJust $ iDerCI st) $ do
    let d = fromJust $ iDerCI st
        dirCheck = dir ++ "-check"
    saveObservation dirCheck d
    putStrLn $ "Check results saved in " ++ dirCheck
  return $ st {iDir = dir}

actView :: IState -> IO IState
actView st
  | iDir st == "" = do
    putStrLn "Nothing to view. Save a derivation first."
    return st
  | otherwise = do
    let cmd = "sleep 1; eog " ++ iDir st ++ "/*.png "
    (void $ runCommand cmd) `catch` (print :: SomeException -> IO ())
    return st

actExit :: IState -> IO IState
actExit _ = putStrLn bye >> exitSuccess

actHelp :: IState -> IO IState
actHelp st = do
  putStrLn $ "Available commands:" ++
             "\n\tload\n\tprogram\n\tgoal\n\tsearch\n\tsave\n\tview" ++
             "\n\texit\n\thelp"
  return st

act :: String -> IState -> IO IState
act ""           = return
act "load"       = actLoad
act "program"    = actProgram
act "goal"       = actGoal
act "check"      = actCheck
act "search"     = actSearch
act "save"       = actSave
act "view"       = actView
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
  let (cs, gs) = parseItems inp
      pr           = Program $ Array.listArray (0, length cs - 1) cs
      st           = iState0 {iProg = Just pr, iGoals = gs}
      (grdLevel, grdCont) = (abs &&& (>= 0)) $ optGuards op
      grd = all (\f -> f pr) $
            take grdLevel [const True {-FIXME-}, guardedMatch, guardedResolution]
  when (grdLevel /= 0 && optVerbose op > 0) $
    putStrLn $ "Level " ++ show grdLevel ++ " guardedness check " ++
               if grd then "PASSED." else "FAILED."
  if grdCont && grd
    then
      actSearch st >>=
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

interactiveLoad :: CmdOptions -> IO IState
interactiveLoad op =
  putStrLn welcome >>
  actLoadFromTerminal op iState0 >>=
  goCoALP

interactiveLoadRun :: CmdOptions -> IO IState
interactiveLoadRun op =
  putStrLn welcome >>
  actLoadFromTerminal op iState0 >>=
  actSearch >>=
  goCoALP

interactiveLoadRunViewAll :: CmdOptions -> IO IState
interactiveLoadRunViewAll op =
  putStrLn welcome >>
  actLoadFromTerminal op iState0 >>=
  actSearch >>=
  actSave >>=
  actView >>=
  goCoALP

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
  | not (optRun op) && not (optView op) = interactiveLoad op
  | optRun op && not (optView op) = interactiveLoadRun op
  | optRun op && optView op && (optGraphics op == "all") =
    interactiveLoadRunViewAll op
  | optRun op && optView op && (optGraphics op == "final") =
    -- TODO: implement (without All)
    interactiveLoadRunViewAll op
goOptions _ = interactiveOptionNotValid

main :: IO IState
main =  parseOptions >>= goOptions
