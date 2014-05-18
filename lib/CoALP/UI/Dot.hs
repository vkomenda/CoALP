-- |
-- * Graphical tree printer

module CoALP.UI.Dot where

import Prelude hiding (mapM_)

import CoALP
import CoALP.UI.Printer ()

import Control.Applicative ((<$>))
import Data.Foldable
import qualified Data.HashMap.Lazy as Map
import System.Process
import System.Directory
import Control.Exception
import Control.Monad (void)
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set

-- | Renders a tree as a string in the ImageMagick dot format.
render :: ONode Occ -> String
render t0 = "digraph G {\n" ++ snd (go t0 0) ++ "}"
  where
    go :: ONode Occ -> Int -> (Int, String)
    go (ONode []) start =
      (start + 1, show start ++
                  "[shape=square,width=.2,label=\"\",fixedsize=true];\n")
    go (ONode ts) start =
      let (next, dot) = connect goA ts (start + 1) start in
      (next, show start ++ " [shape=point];\n" ++ dot)
    goA (ANode occ its) start =
      let (next, dot) = connect go (snd <$> Map.toList its) (start + 1) start in
      (next, show start ++ " [shape=none,label=\"" ++
             show (oTerm occ) ++ "\"];\n" ++ dot)

--    connect :: [ONode Occ] -> Int -> Int -> (Int, String)
    connect fstep ts start parent =
      foldl' (\(start_t, dot) t ->
               let (next, dot_t) = fstep t start_t in
               (next, dot ++ dot_t ++ show parent ++ " -> " ++ show start_t ++
                      "[arrowhead=none];\n"))
             (start, "") ts

-- | Saves a derivation rendered in the dot format in a specified directory, in
-- a set of PNG files therein.
save :: String -> [HashSet (ONode Occ)] -> IO ()
save dir tts =
  flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    mapM_ wr (idx $ Set.toList <$> tts)
  where
    wr (ts, i) =
      mapM_ (\(t, j) -> do
                let base = dir ++ "/" ++ show i ++ "-" ++ show j
                writeFile (base ++ ".gv") (render t)
                void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++
                                     base ++ ".png")
            (idx ts)
    idx :: [a] -> [(a, Int)]
    idx l = zip l [0..]
    
saveFinal :: String -> [HashSet (ONode Occ)] -> IO ()
saveFinal dir tts =
   flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    wr (last (idx $ Set.toList <$> tts))
  where
    wr (ts, i) =
      mapM_ (\(t, j) -> do
                let base = dir ++ "/" ++ show i ++ "-" ++ show j
                writeFile (base ++ ".gv") (render t)
                void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++
                                     base ++ ".png")
            (idx ts)
    idx :: [a] -> [(a, Int)]
    idx l = zip l [0..]
