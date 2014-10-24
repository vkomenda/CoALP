{-# LANGUAGE FlexibleContexts #-}

module CoALP.UI.Parser where

import Text.Parsec
import Text.Parsec.Prim
import Data.Functor.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ( (<*) )
import Control.Monad.State.Lazy
import Data.List (sortBy)

import CoALP.CTree
import CoALP.TermTree
import CoALP.ClauseTree


--------------------------------------------------------------------------------
------------------------------TPS Def and Basics--------------------------------
--------------------------------------------------------------------------------

data TermParserSt = TPS {domainMap :: Map.Map [Int] String, parent :: [Int], child :: [Int], root :: Bool} deriving (Show)
type TermParser = ParsecT String TermParserSt Identity

-- Creates an initial TPS
tpsInit :: TermParserSt
tpsInit = TPS Map.empty [] [1] False

-- resets the state to the initial TPS
forgetVars :: TermParser ()
forgetVars = putState tpsInit

--------------------------------------------------------------------------------
--------------------------Parsers for smallest elements-------------------------
--------------------------------------------------------------------------------

-- Variable consists of a capital letter followed by a sequence of letters, valid symbols and digits
variable :: TermParser ()
variable = do
  first <- upper
  rest <- identRest
  current <- getState
  let expr = first:rest
      newDomain = parent current ++ [last (child current)]
      newChildCount = init (child current) ++ [last (child current) + 1]
  putState $ TPS (Map.insert newDomain expr (domainMap current)) (parent current) newChildCount (root current)
  spaces
  return ()

-- Function consists of a lower case letter, valid symbol or digit followed by a sequence of letters, valid symbols and digits
-- This occurence is called when there are no arugments for this function
function :: TermParser ()
function = do
  first <- lower <|> symbolP <|> digit
  rest <- identRest
  current <- getState
  let expr = first:rest
      newDomain = parent current ++ [last (child current)]
      newChildCount = init (child current) ++ [last (child current) + 1]
  if (root current)
  then putState $ TPS (Map.insert newDomain expr (domainMap current)) (parent current) newChildCount True
  else putState $ TPS (Map.insert [] expr (domainMap current)) [] newChildCount True
  spaces
  return ()

-- This occurence is called when there are arguments for this function
function' :: TermParser ()
function' = do
  first <- lower <|> symbolP <|> digit
  rest <- identRest
  current <- getState
  let expr = first:rest
      newDomain = parent current ++ [last (child current)]
      newChildCount = child current ++ [1]
  if (root current)
  then putState $ TPS (Map.insert newDomain expr (domainMap current)) newDomain newChildCount True
  else putState $ TPS (Map.insert [] expr (domainMap current)) [] newChildCount True
  spaces
  return ()

-- Parenthesis
parenOpen, parenClose :: TermParser ()
parenOpen  = char '(' >> spaces
parenClose = char ')' >> spaces

period :: TermParser ()
period = char '.' >> spaces

comma :: TermParser ()
comma = char ',' >> spaces

-- any sequence of letters, valid symbols or digits
identRest :: TermParser String
identRest = many (letter <|> symbolP <|> digit)

-- Valid symbols
symbolP :: TermParser Char
symbolP = oneOf "!#$%&|*+-/<=>?@^_~"

-- Each Clause which has a head and a body is seperated by :-
from :: TermParser ()
from = string ":-" >> spaces

-- Comments
comment :: TermParser ()
comment = char '%' >> void (anyChar `manyTill`
                            try (void (newline >> spaces) <|> eof))

--------------------------------------------------------------------------------
-------------------------------Parsers for Terms--------------------------------
--------------------------------------------------------------------------------

-- Arguments are between open and closed parenthesis and each is a term seperated by commas
args :: TermParser [TermTree]
args = do
  tt <- between parenOpen parenClose $ (term <* spaces) `sepBy` comma
  current <- getState
  let updChild = (init (child current))
      newChild = init updChild ++ [last updChild +1]
  putState $ TPS (domainMap current) (init2 (parent current)) newChild (root current)
  return $ tt

init2 [] = []
init2 x = init x

-- If the function has arguments
app :: TermParser ()
app = do
  c <- function'
  a <- args
  return ()

-- Term is either a function with arguments, a function without arguments or a variable
term :: TermParser TermTree
term = do
  t <- try app <|> function <|> variable
  st <- getState
  let map = domainMap st
      tt = makeTermTree map
  return $ tt

-- Resets the state between terms in a clause
term' :: TermParser TermTree
term' = do
  b <- forgetVars
  t <- term
  return $ t

-- Only parses terms into a list of TermTrees
onlyTerms :: TermParser [TermTree]
onlyTerms = do
  ts <- many term
  return ts

stateTerms :: TermParser TermParserSt
stateTerms = do
  ts <- many term
  st <- getState
  return st

--------------------------------------------------------------------------------
----------------------Coinductive Term Parser-----------------------------------
--------------------------------------------------------------------------------

-- Each coinductive stae=tement starts with a coinductive
coinductive :: TermParser ()
coinductive = string "coinductive" >> spaces

coTerm :: TermParser String
coTerm = do
  spaces >> coinductive
  b <- between parenOpen parenClose $ identRest
  endCoT
  return $ b

endCoT :: TermParser ()
endCoT = string ":-." >> spaces

onlyCoIn :: TermParser String
onlyCoIn = coTerm <* eof
--------------------------------------------------------------------------------
---------------------------------Goal parsers-----------------------------------
--------------------------------------------------------------------------------

-- A goal starts with a :- and then is any number of terms seperated by commas
goal :: TermParser [TermTree]
goal = do
  spaces >> from
  b <- (term' <* spaces) `sepBy` comma
  period
  return $ b

-- Only parses a goal
onlyGoal :: TermParser [TermTree]
onlyGoal = goal <* eof

--------------------------------------------------------------------------------
--------------------------------Clause parsers----------------------------------
--------------------------------------------------------------------------------

-- Body starts with seperater and any number of spaces then any number of terms seperated by commas until a period
body ::  TermParser [TermTree]
body = from >> spaces >> ((term' <* spaces) `sepBy` comma) <* period

-- Clause is either a term with a body or a term on it's own
clause :: TermParser (ClauseTree)
clause = do
  fv <- forgetVars
  h <- term
  spaces
  b <- try (period >> return []) <|> body
  if b == []
  then return $ makeClauseTree (h:[trueTT])
  else return $ makeClauseTree (h:b)

-- Program is a list of clauses
program :: TermParser [ClauseTree]
program = spaces >> clause `sepEndBy` forgetVars

-- Parses the program until the end of file
onlyProgram :: TermParser [ClauseTree]
onlyProgram = program <* eof

onlyProgramSt :: TermParser ([ClauseTree], TermParserSt)
onlyProgramSt = do
  pr <- onlyProgram
  st <- getState
  return (pr, st)

--------------------------------------------------------------------------------
--------------------------------General Parsing---------------------------------
--------------------------------------------------------------------------------

-- | The parsing engine with the user state of type 'TermParserSt', starting
-- from the initial state.
termParse :: (Stream s Identity t) => Parsec s TermParserSt a -> SourceName -> s -> Either ParseError a
termParse p = runP p tpsInit

-- | The parsing engine with the user state of type 'TermParserSt', starting
-- from a given state.
termParseSt :: (Stream s Identity t) => Parsec s TermParserSt a -> TermParserSt -> SourceName -> s -> Either ParseError a
termParseSt = runP

--------------------------------------------------------------------------------
-------------------------------Parsing from File--------------------------------
--------------------------------------------------------------------------------

-- Reads the file and attempts to parse
termParseFileStCases :: TermParser a -> TermParserSt -> SourceName -> String -> IO a
termParseFileStCases pf tps lab fileName = do
  s <- readFile fileName
  case termParseSt pf tps lab s of
    Left e  -> print e >> fail "parse error"
    Right r -> return r

-- Provides parsing from a file for a range of parses
termParseFileCases :: TermParser a -> SourceName -> String -> IO a
termParseFileCases pf = termParseFileStCases pf tpsInit

-- Parses a program from a file
programFromFile :: String -> IO [ClauseTree]
programFromFile = termParseFileCases onlyProgram "program"

--------------------------------------------------------------------------------
------------------------------Parsing from String-------------------------------
--------------------------------------------------------------------------------

-- Attempts to parse the string
termParseStCases :: TermParser a -> TermParserSt -> SourceName -> String -> a
termParseStCases pf tps lab txt =
  case termParseSt pf tps lab txt of
    Left e  -> error $ show e
    Right r -> r

-- Provides parsing from a String for a range of parses
termParseCases :: TermParser a -> SourceName -> String -> a
termParseCases pf = termParseStCases pf tpsInit

fromStringSt :: TermParser a -> TermParserSt -> String -> a
fromStringSt f tps = termParseStCases f tps "fromStringSt"

-- Parses a program from a String
programFromString :: String -> [ClauseTree]
programFromString = termParseCases onlyProgram "program"


--------------------------------------------------------------------------------
------------------------Definition for items in a prog--------------------------
--------------------------------------------------------------------------------

-- | Top-level syntactic items present in input text.
data Item = ItemClause    ClauseTree
          | ItemGoal      [TermTree]
          -- | ItemModeAssoc ModeAssoc
          | ItemCoTerm    String
          | ItemComment   ()            -- ^ forgets comments
          deriving (Eq, Show)

-- | Unordered top-level syntactic items.
items :: TermParser [Item]
items =
  many1
  (
    coTerm    `as` ItemCoTerm    <|>
    clause    `as` ItemClause    <|>
    goal      `as` ItemGoal      <|>
    -- modeAssoc `as` ItemModeAssoc <|>
    comment   `as` ItemComment   <|>
    unexpected "Unexpected item in bagging area :)"
  )
  where
    f `as` g = try $ f >>= return . g

--------------------------------------------------------------------------------
-----------------------------Parsing a full program-----------------------------
--------------------------------------------------------------------------------

-- | Categorisation function that applies after items have been retrieved from a
-- string or from a file.
groupItems :: [Item] -> ([ClauseTree], [[TermTree]], [String])
groupItems = foldr ins ([], [], [])
  where
    ins (ItemClause    c) (cs, gs, cts) = (c:cs, gs, cts)
    ins (ItemGoal      g) (cs, gs, cts) = (cs, g:gs, cts)
    --ins (ItemModeAssoc m) (cs, gs, ms) = (cs, gs, m:ms)
    ins (ItemCoTerm   ct) (cs, gs, cts) = (cs, gs, ct:cts)
    ins (ItemComment   _) old           = old

-- Ensures all the Term trees share the same signature (ranked alphabet) as arity must be consistent
unifySignature :: ([ClauseTree], [[TermTree]], [String]) -> ([ClauseTree], [[TermTree]], [String])
unifySignature (cts, tts, cots) =
  let ctRA = mergeCTRA cts
      ttRA = mergeRankAlpha $ map (mergeTTRA) tts
      newRA = mergeRankedAlpha ctRA ttRA
  in  (map (flip replaceCLTreeRA newRA) cts, map (flip replaceTTreeRA newRA) tts, cots)

-- Parses a String into a list of Items
itemsString :: String -> [Item]
itemsString = termParseCases items "items"

-- Parses a file into a list of Items
itemsFile :: String -> IO [Item]
itemsFile = termParseFileCases items "items"

-- Parses a file into a tuple with a Program and a Goal
parseItemsFile :: String -> IO ([ClauseTree], [[TermTree]], [String])
parseItemsFile fn = itemsFile fn >>= return . unifySignature . groupItems

-- Parses a string into a tuple with a Program and a Goal
parseItems :: String -> ([ClauseTree], [[TermTree]], [String])
parseItems = unifySignature . groupItems . itemsString

--------------------------------------------------------------------------------
-----------------------------------Testing--------------------------------------
--------------------------------------------------------------------------------

-- Tries to parse a string into a TermTree
parseTerm :: String -> [TermTree]
parseTerm t = either (\_ -> [empty]) id $ runP onlyTerms tpsInit "" t

-- Tries to parse a string into a ClauseTree
parseClause :: String -> ClauseTree
parseClause c = either (\_ -> empty) id $ runP clause tpsInit "" c

-- Tries to parse a string into a list of ClauseTrees
parseProg :: String -> [ClauseTree]
parseProg p =  either (\_ -> [empty]) id $ runP program tpsInit "" p

drawItems :: ([ClauseTree], [[TermTree]], [String]) -> IO ()
drawItems (prg, gs, cots) = do
  putStrLn "Program : "
  drawProgram prg
  putStrLn "Goals : "
  drawGoals gs
  if cots == []
  then return ()
  else do putStrLn "Coinductive terms : "
          putStrLn $ concat $ ((map (++ ",") (init cots)) ++ [(last cots)])
