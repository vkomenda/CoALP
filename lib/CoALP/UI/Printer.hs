{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- |
-- * Term printers

module CoALP.UI.Printer where

import CoALP
import Data.List (intercalate)
import Control.Applicative ( (<$>) )
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Lazy as IntMap

-- | A type class to avoid quotes on strings that 'show' introduces. Instances
-- of 'ShowNoQ' on types except for 'String' can be equivalent to the usual
-- instances of 'Show' on those types.
class ShowNoQ a where
  show0 :: a -> String

instance ShowNoQ String where
  show0 = id

instance (ShowNoQ a, Show b) => Show (Term a b) where
  show (Var v)    = "X_" ++ show v
  show (Fun c []) = show0 c
  show (Fun c ts) = show0 c ++ " (" ++ intercalate ", " (show <$> ts) ++ ")"

instance Show Subst1 where
  show (Subst s) = show s

instance (ShowNoQ a, Show b) => Show (Clause a b) where
  show (t :- []) = show t ++ "."
  show (t :- ts) = show t ++ " :- " ++ intercalate ", " (show <$> ts) ++ "."

instance (ShowNoQ a, Show b) => Show (Program a b) where
  show (Pr []) = "(empty)"
  show (Pr pr) = intercalate "\n" $ show <$> pr

instance (ShowNoQ a, Show b) => Show (Goal a b) where
  show (Go []) = ":- ."
  show (Go g)  = ":- " ++ intercalate ", " (show <$> g) ++ "."

instance Show Mode where
  show (M d o) = show d ++ show o

instance Show Direction where
  show Input  = "+"
  show Output = "-"

instance Show ModeAssoc where
  show (ModeAssoc ma) =
    concatMap
      (\(ident, mss) ->
        concatMap (\modes ->
                    ident ++ " (" ++ (intercalate ", " $ map show modes) ++ ")\n")
                  (HashSet.toList mss))
      (HashMap.toList ma)

instance (Show a, Pathed a) => Show (ANode a) where
  show (ANode a ns) =
    p ++ " AND " ++ show a ++ "\n" ++
    intercalate "\n" ((\(i, n) -> p ++ show i ++ ". " ++ show n) <$>
                      HashMap.toList ns)
    where
      p = foldr (\s -> (++) (s ++ ".")) "" $ show <$> path a

instance (Show a, Pathed a) => Show (ONode a) where
  show (ONode []) = "VOID\n"
  show (ONode ns) =
    "OR\n" ++ concatMap show ns


instance Show Occ where
  show Occ
       {
         oTerm = t
       , oMods = m
--       , oPos = p
       , oTodo = d
       , oVars = v
       } =
    "{{{ " ++
    intercalate ", "
    [
      "term = "            ++ show t
    , "argument modes = "  ++ show m
--    , "tree path = "       ++ show p
    , "todo clauses = "    ++ show (IntSet.toList d)
    , "moded variables = " ++ show (IntMap.toList v)
    ] ++ " }}}"
