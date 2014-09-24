{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module CoALP.UI.Printer where

import CoALP.CTree
import CoALP.Substitution
import Data.List (intercalate)

-- | A type class to avoid quotes on strings that 'show' introduces. Instances
-- of 'ShowNoQ' on types except for 'String' can be equivalent to the usual
-- instances of 'Show' on those types.
class ShowNoQ a where
  show0 :: a -> String

instance ShowNoQ String where
  show0 = id

instance ShowNoQ (CTree String) where
  show0 = convertToFnString [[]]

instance ShowNoQ SubstTree where
  show0 = show0 . fmap'' (show0)

instance ShowNoQ (Int, Subst) where
  show0 (i,s) = "< " ++ show i ++ ", " ++ substToString s ++ " >"

instance ShowNoQ Subst where
  show0 s = substToString s

instance ShowNoQ (Int,[([Int], CTree String)]) where
   show0 (i, rs) = show i ++ ", (" ++ intercalate ", " (map (show0) rs) ++ ")."

instance ShowNoQ ([Int], CTree String) where
  show0 (d,tt) = show d ++ ", " ++ show0 tt
