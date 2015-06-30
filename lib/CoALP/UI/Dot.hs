-- |
-- * Graphical tree printer

module CoALP.UI.Dot where

import Prelude hiding (sequence_, concatMap)

import CoALP
import CoALP.UI.Printer ()

import Control.Applicative ((<$>))
import Data.Array (Array, (!))
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
render t0 = "digraph G {\nnode [shape=plaintext];\n" ++ goA [] t0 ++ "}"
  where
    showPath :: Path -> String
    showPath w = intercalate "_" $ show <$> w

    rootTag :: String
    rootTag = "root"

    goA :: Path -> TreeOper1 -> String
    goA w (NodeOper a b) =
      tag w ++ " [label=" ++
      "<<table border=\"0\" cellborder=\"1\" cellspacing=\"0\">\n" ++
      "<tr><td port=\"term\" colspan=\"" ++ len ++ "\">" ++
      show a ++ "</td></tr>\n" ++ "<tr>\n" ++
      concatMap peekB bs ++
      "</tr>\n" ++
      "</table>>];\n" ++
      lastLink w ++
      concatMap (goB w) bs
      where
        len = show $ 1 + (uncurry (flip (-)) (Array.bounds b))
        bs = Array.assocs b

    tag [] = rootTag
    tag w  = rootTag ++ "_" ++ showPath w

    lastLink w =
      if not (null w) && not (null (init w))
      then tag (init (init w)) ++ ":" ++ show (last (init w)) ++ " -> " ++
           tag w ++ ":term\n"
      else ""

    peekB :: (Int, Oper [TreeOper1]) -> String
    peekB (_, Right (Just []))  = "<td>QED</td>\n"
    peekB (i, Right (Just ts))  = "<td port=\"" ++ show i ++
                                  "\">" ++ show i ++ "</td>\n"
    peekB (i, Right Nothing)    = "<td bgcolor=\"grey\"></td>\n"
    peekB (_, Left ToBeMatched) = "<td>TBM</td>\n"
    peekB (_, Left ToBeUnified) = "<td>TBU</td>\n"

    goB :: Path -> (Int, Oper [TreeOper1]) -> String
    goB w (i, Right (Just ts@(_:_))) =
      concatMap (\(j, t) -> goA (w ++ [i, j]) t) (zip [0..] ts)
    goB _ _ = ""

-- | Renders derivation overview.
renderDerivation :: Derivation TreeOper1 Transition TreeOper1 -> String
renderDerivation d =
  TextDot.showDot $ Dot.fglToDotGeneric g showGoals showTransition id
  where
    g = derivation d
    showTransition r = show r
    showGoals :: TreeOper1 -> String
    showGoals t = showOperTerm $ (nodeBundleOper t)!0
    showOperTerm :: Oper [TreeOper1] -> String
    showOperTerm (Right (Just ts)) = intercalate "\n" $
                                     ((show . nodeTermOper) <$> ts)
    showOperTerm _ = "n/a"

-- | Saves a derivation rendered in the dot format in a specified directory, in
-- a set of PNG files therein.
save :: String -> Derivation TreeOper1 Transition TreeOper1 -> IO ()
save dir d =
  flip catch (print :: IOError -> IO ()) $ do
    createDirectory dir
    writeFile (overview ++ extension) $ renderDerivation d
    sequence_ $ (\(i, t) -> writeFile (base ++ show i ++ extension) $ render t
                ) <$> Graph.labNodes (derivation d)
    void $ runCommand convAll
  where
    extension = ".gv"
    base = dir ++ "/"
    overview = base ++ "overview"
    convAll = "dot -Tpng " ++ base ++ "*" ++ extension ++ " -O"
