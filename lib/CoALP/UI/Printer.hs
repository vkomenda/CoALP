{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- |
-- * Term printers

module CoALP.UI.Printer where

import CoALP
import Data.List (intercalate)
import Control.Applicative ( (<$>) )
import qualified Data.Array as Array
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet

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
  show (Fun c ts) = show0 c ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

instance (ShowNoQ a, Show b) => Show (Clause a b) where
  show (t :- []) = show t ++ "."
  show (t :- ts) = show t ++ " :- " ++ intercalate ", " (show <$> ts) ++ "."

instance (ShowNoQ a, Show b) => Show (Program a b) where
  show (Program cls) | null (Array.elems cls) = "(empty)"
                     | otherwise = intercalate "\n" $ show <$> Array.elems cls

instance (ShowNoQ a, Show b) => Show (Goal a b) where
  show (Goal []) = ":- ."
  show (Goal g)  = ":- " ++ intercalate ", " (show <$> g) ++ "."

instance (ShowNoQ a, Show b) => Show (Subst (Term a) b b) where
  show s = intercalate ", " $
           (\(i, a) -> show a ++ "/" ++ show i
           ) <$> HashMap.toList (unSubst s)

instance (Show a) => Show (TreeOper a) where
  show t = goA [] t
    where
      goA prefix (NodeOper a b) =
        "\n" ++ show prefix ++ " AND " ++ show a ++ "\n" ++
        (intercalate "\n" $
         (\(i, oper) -> show (prefix ++ [i]) ++ goB (prefix ++ [i]) oper) <$>
         Array.assocs b)
      goB _      (Right (Just [])) = " QED"
      goB prefix (Right (Just ts)) =
        " OR" ++
        (\(j, u) -> goA (prefix ++ [j]) u) `concatMap` (zip [0..] ts)
      goB _      (Right Nothing) = " NOT UNIFIABLE"
      goB _      (Left ToBeMatched) = " TO BE MATCHED"
      goB _      (Left ToBeUnified) = " TO BE UNIFIED"

instance Show Transition where
  show r =
    "(" ++ show (transitionPath r) ++ " <- " ++ show (transitionSubst r) ++ ")"

instance Show Guard where
  show (Guard i w a) = "(" ++ show i ++ " :guarded at: " ++
                       show w ++ " :by: " ++ show a

instance Show Invariant where
  show (Invariant i gs) = "(" ++ show i ++ " :invariant: " ++
                          show (HashSet.toList gs) ++ ")"

instance Show TransGuards where
  show r =
    "(" ++ show (transPath r) ++ " <- " ++ show (transSubst r) ++ " | " ++
    show (HashSet.toList $ transGuards r) ++ ")"
