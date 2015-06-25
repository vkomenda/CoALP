-- | Command-line option parser.

module CoALP.Interpreter.Options
       (
         CmdOptions (..)
       , parseOptions
       )
       where

import Options.Applicative

data CmdOptions = CmdOptions
  {
    optStdin    :: Bool
  , optLoad     :: String
  , optRun      :: Bool
  , optView     :: Bool
  , optGraphics :: String
  , optGuards   :: Int
  , optVerbose  :: Int
  }
  deriving Show

parseCmdOption :: Parser CmdOptions
parseCmdOption = CmdOptions
     <$> switch
         ( long "stdin"
        <> short 'n'
        <> help "Start in the non-interactive mode and read input from stdin." )
     <*> strOption
         ( long "load"
        <> short 'l'
        <> value ""
        <> help "Load a file." )
    <*> switch
         ( long "run"
        <> short 'r'
        <> help "Run the derivation." )
    <*> switch
         ( long "view"
        <> help ("View the result of a derivation. " ++
                 "This option is only available if run is given.") )
    <*> strOption
         ( long "graphics"
        <> short 'g'
        <> value "final"
        <> help ("Which of the results to save as pictures: either \"all\" " ++
                 "or \"final\" (default). Requires Graphviz.") )
    <*> option auto
         ( long "guards"
        <> short 'a'
        <> value 3
        <> help ("Guardedness check level: 0 (no check), 1 (placeholder), " ++
                 "2 (program), 3 (derivation). Add the minus sign to run " ++
                 "guardedness checks alone, without a following derivation.") )
    <*> option auto
         ( long "verbose"
        <> short 'v'
        <> value 1
        <> help "The verbosity level." )

opts :: ParserInfo CmdOptions
opts = info (parseCmdOption <**> helper)
  ( fullDesc
 <> progDesc "Options for CoALP")

parseOptions :: IO CmdOptions
parseOptions = execParser opts
