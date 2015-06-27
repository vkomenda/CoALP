-- |
-- * Graphical tree printer

module CoALP.UI.Dot where

import Prelude hiding (mapM_, concat)

import CoALP
import CoALP.UI.Printer ()

import Control.Applicative ((<$>))
import Data.Array ((!))
import qualified Data.Array as Array
import Data.Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Dot as Dot
import Data.List (intercalate)
import qualified Text.Dot as TextDot
import System.Process
import System.Directory
import Control.Exception
import Control.Monad (void)

-- | Renders a tree as a string in the ImageMagick dot format.
render :: TreeOper1 -> String
render t0 = "digraph G {\n" ++ snd (goA t0 0) ++ "}"
  where
    goA :: TreeOper1 -> Int -> (Int, String)
    goA (NodeOper a b) start =
      let (next, dot) = connect goB (Array.elems b) (start + 1) start in
      (next, show start ++ " [shape=none,label=\"" ++
             show a ++ "\"];\n" ++ dot)

    goB :: Oper [TreeOper1] -> Int -> (Int, String)
    goB (Right (Just [])) start =
      (start + 1, show start ++
                  "[shape=square,width=.2,label=\"\",fixedsize=true];\n")
    goB (Right (Just ts)) start =
      let (next, dot) = connect goA ts (start + 1) start in
       (next, show start ++ " [shape=point];\n" ++ dot)
    goB (Right Nothing) start =
      (start + 1, show start ++
                  "[shape=circle,width=.2,label=\"\",fixedsize=true];\n")
    goB (Left ToBeMatched) start =
      (start + 1, show start ++
                  "[shape=square,width=.2,label=\"!\",fixedsize=true];\n")
    goB (Left ToBeUnified) start =
      (start + 1, show start ++
                  "[shape=square,width=.2,label=\"?\",fixedsize=true];\n")

    connect fstep ts start parent =
      foldl' (\(start_t, dot) t ->
               let (next, dot_t) = fstep t start_t in
               (next, dot ++ dot_t ++ show parent ++ " -> " ++ show start_t ++
                      "[arrowhead=none];\n"))
             (start, "") ts

-- | Renders derivation overview.
renderDerivation :: Derivation TreeOper1 -> String
renderDerivation d =
  TextDot.showDot $ Dot.fglToDotGeneric g showGoals showTransition id
  where
    g = derivation d
    showTransition r = show r
    showGoals :: TreeOper1 -> String
    showGoals t = showOperTerm $ (nodeBundleOper t)!0
    showOperTerm :: Oper [TreeOper1] -> String
    showOperTerm (Right (Just ts)) = intercalate "; " $
                                     ((show . nodeTermOper) <$> ts)
    showOperTerm _ = "n/a"

-- | Saves a derivation rendered in the dot format in a specified directory, in
-- a set of PNG files therein.
save :: String -> Derivation TreeOper1 -> IO ()
save dir d =
  flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    writeFile (base ++ ".gv") $ renderDerivation d
    void $ runCommand $ "dot -Tpng " ++ base ++ ".gv -o " ++ base ++ ".png"
  where
    base = dir ++ "/" ++ "overview"
