module CoALP.Clause where

import CoALP.Term as Term
import CoALP.Subst as Subst

import Control.DeepSeq
import Data.Foldable (foldMap)

infixr 3 :-

data Clause a b = Term a b :- [Term a b]
type Clause1 = Clause String Int

instance (Eq a, Eq b) => Eq (Clause a b)

instance (NFData a, NFData b) => NFData (Clause a b)

instance Functor (Clause a) where
  fmap f (h :- t) = fmap f h :- map (fmap f) t

clHead :: Clause a b -> Term a b
clHead (h :- _) = h

clBody :: Clause a b -> [Term a b]
clBody (_ :- b) = b

clSubst :: Subst1 -> Clause1 -> Clause1
clSubst s (h :- b) = (h >>= subst s) :- map (>>= subst s) b

newtype Program a b = Pr {unPr :: [Clause a b]}
type Program1 = Program String Int

instance (NFData a, NFData b) => NFData (Program a b)

clBodyI :: Program a b -> Int -> [(Int, Term a b)]
clBodyI pr i = zip [0..] (clBody $ (unPr pr)!!i)

newtype Goal a b = Go {unGo :: [Term a b]}
type Goal1 = Goal String Int

instance (Eq a, Eq b) => Eq (Goal a b)

instance (NFData a, NFData b) => NFData (Goal a b)

varsClause1 :: Clause1 -> VarSet
varsClause1 (h :- b) = foldMap varsTerm1 (h:b)

liftVarsClause1 :: Maybe Int -> Clause1 -> Clause1
liftVarsClause1 Nothing  = id
liftVarsClause1 (Just n) = fmap (+ n)

liftVarsClause :: Num b => Maybe b -> Clause a b -> Clause a b
liftVarsClause Nothing  = id
liftVarsClause (Just n) = fmap (+ n)
