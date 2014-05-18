{-# LANGUAGE TupleSections#-}

-- |
-- * Trees and derivations

module CoALP.Tree where

import Prelude hiding (concat, concatMap, foldr, foldl, maximum, all, any, elem)

import CoALP.Term as Term
import CoALP.Subst
import CoALP.Clause
import CoALP.Mode

import Control.DeepSeq
--import Data.Bits
import Data.Maybe
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.List (intersect)
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Control.Applicative

-- | @ANode a its@ is an atom with a possibly partial mapping from clauses to
-- or-subtrees. Each of those or-subtrees corresponds to some clause number @i@
-- such that the head of that clause has been unified with @a@ and its unified
-- body atoms label the roots of the and-subtrees of the @i@-th 'OrNode'.
data ANode a = ANode a (HashMap Int (ONode a))
             deriving (Eq)

-- | @ONode ts@ is the or-subtree corresponding to unification against a clause
-- in the logic program where @ts@ are the trees built by matching against the
-- body terms of that clause.
--
-- A separate case is the topmost 'ONode' which contains the list of _goals_ to
-- be unified against a logic program.
data ONode a = ONode [ANode a]
             deriving (Eq)

instance (Hashable t) => Hashable (ANode t) where
  hashWithSalt s (ANode t its) =
    s `hashWithSalt` t `hashWithSalt`
    (HashMap.foldrWithKey (\i _ h -> h `hashWithSalt` i) 0x42D2 its)
{-
  hash (ANode t its) =
    hash t `xor` (HashMap.foldrWithKey (\i _ h -> (h `rotate` 1) `xor` hash i)
                                       0x42D2 its)
-}

instance (Hashable t) => Hashable (ONode t) where
  hashWithSalt s (ONode ts) = s `hashWithSalt` (foldr (flip hashWithSalt) 0x0420 ts)
{-
  hash           (ONode ts) = foldr (xor . hash) 0x0420 ts
-}

instance NFData (ANode t)
instance NFData (ONode t)

instance Functor ANode where
  fmap f (ANode t its) = ANode (f t) (fmap (fmap f) its)

instance Functor ONode where
  fmap f (ONode    ts) = ONode       (fmap (fmap f)  ts)

instance Foldable ANode where
  foldr f z (ANode t its) = f t $ foldr (flip (foldr f)) z its

instance Foldable ONode where
  foldr f z (ONode    ts) =       foldr (flip (foldr f)) z  ts

instance Traversable ANode where
  traverse f (ANode t its) = ANode <$> f t <*> traverse (traverse f) its

instance Traversable ONode where
  traverse f (ONode    ts) = ONode <$>         traverse (traverse f)  ts

-- | The way to identify the position of a node in a tree is to specify the path
-- to it through labelled branches from the root.
type TreePath = [Int]

type ModedVars = IntMap Mode

-- | Term occurrence.
data Occ = Occ
           {
             oTerm :: Term1    -- ^ term
           , oMods :: [Mode]   -- ^ mode annotations for the arguments
           , oPos  :: TreePath -- ^ position, a path through labelled branches
                               -- from the root
           , oTodo :: IntSet   -- ^ indices of clauses not yet attempted
           , oVars :: ModedVars
                               -- ^ all the variables in the subtree with this
                               -- term occurrence as its root, with associated
                               -- evaluation order (eager or lazy)
           }
         deriving (Eq, Ord)

class Pathed a where
  path :: a -> [Int]

instance Pathed Occ where
  path = oPos

instance Hashable Occ where
  hashWithSalt s Occ {oTerm = t, oPos = p} = s `hashWithSalt` t `hashWithSalt` p
{-
  hash           Occ {oTerm = t, oPos = p} = (hash t `rotate` 7) `xor` hash p
-}

instance NFData Occ

-- | Tree of term occurrences with an 'ONode' in the root.
--type OTree = ONode Occ

-- | Accumulation of a variable renaming over a pair of or-nodes.
renameONode :: ONode Occ -> ONode Occ -> Subst1 -> Maybe Subst1
renameONode (ONode lts) (ONode rts) s = renameANodes lts rts s

-- | Accumulation of a variable renaming over labelled branches of a pair of
-- or-nodes.
renameANodes :: [ANode Occ] -> [ANode Occ] -> Subst1 -> Maybe Subst1
renameANodes [] [] s = Just s
renameANodes (tl:lts) (tr:rts) s = do
  s0 <- renameANode  tl  tr  s
  s1 <- renameANodes lts rts s0
  return $ s0 `compose` s1
renameANodes _ _ _ = Nothing

-- | Accumulation of a variable renaming over a pair of and-nodes.
renameANode :: ANode Occ -> ANode Occ -> Subst1 -> Maybe Subst1
renameANode (ANode locc lits) (ANode rocc rits) s = do
  let appt = (>>= subst s) . oTerm
  s0 <- renameMaybe (appt locc) (appt rocc)
  s1 <- renameONodes (HashMap.toList lits) (HashMap.toList rits) s0
  return $ s0 `compose` s1

-- | Accumulation of a variable renaming over labelled branches of a pair of
-- and-nodes.
renameONodes :: [(Int, ONode Occ)] -> [(Int, ONode Occ)] ->
               Subst1 -> Maybe Subst1
renameONodes [] [] s = Just s
renameONodes ((il,tl):lts) ((ir,tr):rts) s
  | il /= ir = Nothing
  | otherwise = do
    s0 <- renameONode  tl  tr  s
    s1 <- renameONodes lts rts s0
    return $ s0 `compose` s1
renameONodes _ _ _ = Nothing

-- | Equivalence of occurrence trees up to variable renaming.
equiv :: ONode Occ -> ONode Occ -> Bool
equiv tl tr = isJust $ renameONode tl tr identity

-- | Insertion of a tree into a set modulo the equivalence relation.
insertModEquiv :: ONode Occ -> HashSet (ONode Occ) -> HashSet (ONode Occ)
insertModEquiv t ts =
  if HashSet.null $ HashSet.filter (equiv t) ts then
    HashSet.insert t ts
  else ts

-- | Union of two sets of occurrence trees modulo the equivalence relation. It
-- produces a set of non-equivalent trees iff the *first argument* contains no
-- equivalent trees.
unionModEquiv :: HashSet (ONode Occ) -> HashSet (ONode Occ) ->
                 HashSet (ONode Occ)
unionModEquiv =
  foldr (\t s -> if HashSet.null $ HashSet.filter (equiv t) s then
                   HashSet.insert t s
                 else s)

-- | Variables of all the children on an or-node.
varsONode :: ONode Occ -> ModedVars
varsONode (ONode ts) = foldr ((<>) . varsANode) mempty ts

-- | Variables of an and-node and all its children. Computed elsewhere; here
-- they are returned from given.
varsANode :: ANode Occ -> ModedVars
varsANode (ANode occ _) = oVars occ

-- | Maximum variable index of a tree with the given or-node as the root.
maxVarONode :: ONode Occ -> Maybe Int
maxVarONode t = foldr (max . Just) Nothing (fst <$> (IntMap.toList $ varsONode t))

-- | Variables of the topmost terms in the tree.
rootVarsONode :: ONode Occ -> VarSet
rootVarsONode (ONode ts) = foldr ((<>) . rootVarsANode) mempty ts

rootVarsANode :: ANode Occ -> VarSet
rootVarsANode (ANode occ _) = varsTerm1 $ oTerm occ

-- | Root of a tree
rootTree :: ONode Occ -> [Term1]
rootTree (ONode ts) = map rootTreeANode ts

rootTreeANode :: ANode Occ -> Term1
rootTreeANode (ANode occ _) = (oTerm occ)

-- | @unionModedVars vm1 vm2@ produces a mapping that consists of the most
-- concrete mode associations for variable names in @vm1@ or @vm2@.
unionModedVars :: ModedVars -> ModedVars -> ModedVars
unionModedVars = IntMap.mergeWithKey both id id
  where both _ o1 o2 = Just $ min o1 o2

-- | @modedVarsTerm t ms@ computes a variable to mode association for a given
-- term @t@ with n arguments and an n-element list of modes @ms@. This
-- correspondence between @t@ and @ms@ is essential since this function does not
-- guess a mode if a mode association is missing from @ms@, and neither does it
-- deal with too many mode associations in @ms@.
modedVarsTerm :: Term1 -> [Mode] -> ModedVars
modedVarsTerm (Fun _ ts) ms =
  foldr unionModedVars mempty $
  zipWith (\vs m -> IntMap.fromSet (const m) vs) (varsTerm1 <$> ts) ms
modedVarsTerm (Var v) _ =
  error $ "modedVarsTerm: forbidden aplication to a variable " ++ show v

-- | Extends a given tree by subsumption (matching) against a logic program. No
-- substitutions are applied within the tree itself, only within the program
-- clauses whose heads subsume atoms labelling and-nodes of the tree in
-- question.
growByMatchONode :: Program1 -> ModeAssoc -> ONode Occ -> ONode Occ
growByMatchONode pr ma (ONode ts) = ONode $ growByMatchANode pr ma <$> ts

growByMatchANode :: Program1 -> ModeAssoc -> ANode Occ -> ANode Occ
growByMatchANode pr ma (ANode occ@Occ { oTerm = a
                                      , oMods = mods
                                      , oPos = pos
                                      , oTodo = idxs
                                      }
                              its) =
  ANode occ{oTodo = idxs', oVars = vs'} its'
  where
    vs' = modedVarsTerm a mods
          `unionModedVars`
          foldr unionModedVars mempty (varsONode <$> its')
    idxs' = IntSet.difference idxs $
                              foldr (fmitr (\i _ -> IntSet.insert i))
                                    mempty subs
    its' = foldr (fmitr HashMap.insert) its subs
    subs = sub <$> IntSet.toList idxs
    sub i = do
      s <- (clHead $ (unPr pr)!!i) `matchMaybe` a
      return (i, growLeaves pr i $ gr i s)
    gr i s (j, b) = growByMatchANode pr ma $
                    let b' = b >>= subst s
                        mods_b' = argumentModes ma b' in
                    ANode Occ { oTerm = b'
                              , oMods = mods_b'
                              , oPos = pos ++ [i, j]
                              , oTodo = todo0
                              , oVars = modedVarsTerm b' mods_b'}
                          mempty
    fmitr _ Nothing = id
    fmitr f (Just (i,tr)) = f i tr
    todo0 = IntSet.fromList [0..length (unPr pr)-1]

-- | @growLeaves pr i f@ grows leaves that contain instantiated body atoms of
-- the @i@-th clause of the logic program @pr@ applying @f@ to each new leaf.
growLeaves :: Program1 -> Int -> ((Int, Term1) -> ANode Occ) -> ONode Occ
growLeaves pr i f = ONode $ f <$> clBodyI pr i

-- | All mgus of a tree, unified against a program, with associated tree paths
-- to subtrees that should be created when an mgu is applied to the tree.
mgusONode :: Program1 -> ONode Occ ->
             Maybe (HashMap Subst1 (HashSet TreePath))
mgusONode pr (ONode ts)
  | any isNothing mgus1 = Nothing
  | otherwise           = Just $ HashMap.unions $ catMaybes mgus1
  where
    mgus1 = mgusANode pr <$> ts

mgusANode :: Program1 -> ANode Occ -> Maybe (HashMap Subst1 (HashSet TreePath))
mgusANode pr (ANode Occ {oTerm = t, oPos = pos, oTodo = idxs} its)
  | (HashMap.null its && null mgus0)       -- iff this is a failure leaf
    || any isNothing mgus1 = Nothing
  | otherwise = Just $ foldr (HashMap.unionWith HashSet.union)
                             (HashMap.fromList mgus0)
                             (catMaybes mgus1)
  where
    mgus0 :: [(Subst1, HashSet TreePath)]
    mgus0 = mapMaybe mg $ IntSet.toList idxs
    mgus1 :: [Maybe (HashMap Subst1 (HashSet TreePath))]
    mgus1 = mgusONode pr <$> snd <$> HashMap.toList its
    mg :: Int -> Maybe (Subst1, HashSet TreePath)
    mg i = do
      s <- (clHead $ (unPr pr)!!i) `mguMaybe` t
      return (s, HashSet.singleton $ pos ++ [i])

-- | Applies a substitution to a tree given a logic program and extends branches
-- at positions specified in the given set of paths.
applyONode :: Program1 -> ModeAssoc -> Subst1 -> HashSet TreePath ->
              ONode Occ -> ONode Occ
applyONode pr ma s paths (ONode ts) =
  ONode $ applyANode pr ma s paths <$> ts

applyANode :: Program1 -> ModeAssoc -> Subst1 -> HashSet TreePath ->
              ANode Occ -> ANode Occ
applyANode pr ma s paths (ANode Occ {oTerm = a, oPos = pos, oTodo = todo} its) =
  ANode Occ { oTerm = s_a
            , oMods = mods'
            , oPos = pos
            , oTodo = todo'
            , oVars = vs'}
        its'
  where
    s_a = a >>= subst s
    mods' = argumentModes ma s_a
    vs' = modedVarsTerm s_a mods'
          `unionModedVars`
          foldr unionModedVars mempty (varsONode <$> its')
    todo' = IntSet.difference todo quo
    its' = (applyONode pr ma s paths <$> its) <> sprouts
    quo = foldr (\p -> if init p == pos then IntSet.insert $ last p
                       else id) mempty paths
    sprouts = IntSet.foldr (\i -> HashMap.insert i (growLeaves pr i $ sprout i))
                           mempty quo
    sprout i (j, b) =
      let b' = b >>= subst s
          mods_b' = argumentModes ma b' in
      ANode Occ { oTerm = b'
                , oMods = mods_b'
                , oPos  = pos ++ [i, j]
                , oTodo = idxs
                , oVars = modedVarsTerm b' mods_b'}
            mempty
    idxs = IntSet.fromAscList [0..length (unPr pr) - 1]

-- | Grows a forest from a given tree by applying either
--
-- 1. all possible mgus that **do not contain substitutions for lazy
-- variables**, if such mgus exist, or,
--
-- 2. all possible mgus that contain substitutions for lazy variables,
-- otherwise.
--
-- The mgus are computed for a given logic program and association of
-- argument modes to constructors.
growByMgu :: Program1 -> ModeAssoc -> ONode Occ -> HashSet (ONode Occ)
growByMgu pr ma t = case mgusONode pr t of
  Nothing -> HashSet.empty
  Just mg -> let emg = eagerMgus mg in
    if HashMap.null emg then
      app mg
    else
      app emg
  where
    eagerMgus :: HashMap Subst1 a -> HashMap Subst1 a
    eagerMgus = HashMap.filterWithKey $ \(Subst s) _ ->
      null $ HashMap.keys s `intersect` lazyVars
--      all (\v -> applySubst s (Var v) == Var v) lazyVars
    lazyVars :: [Int]
    lazyVars = IntMap.keys $ IntMap.filter (\(M _ o) -> o == Lazy) $ varsONode t
    app :: HashMap Subst1 (HashSet TreePath) -> HashSet (ONode Occ)
    app = HashMap.foldrWithKey
          (\s p -> insertModEquiv $ applyONode pr ma s p t)
          HashSet.empty

{-
-- | The default mode is the strongest mode for the given groundness.
defaultMode :: Term1 -> Mode
defaultMode t | IntSet.null $ varsTerm1 t = M Input Eager
              | otherwise                 = M Output Lazy
-}

-- | Get the list of matching argument modes from the mode association, if such
-- list exists, or return default argument modes otherwise.
--
-- FIXME: remove the mapping of arguments with variables to 'Output'. Input may
-- contain variables as well if it is lazy.
matchModes :: ModeAssoc -> Ident -> [Term1] -> [Mode]
matchModes _ _ [] = []
matchModes (ModeAssoc ma) c ts =
  case ms of
    Nothing -> error $ "Modes not found for " ++ c ++ "/" ++ show l
    Just modes -> modes
  where
    l  = length ts
    ms = do
      byCon <- HashMap.lookup c ma
      let byLen = HashSet.filter ((== l) . length) byCon
          byGround =
            HashSet.filter (\modes ->
                             (\(M d _, closed) -> closed || d == Output)
                             `all`
                             zip modes (IntSet.null . varsTerm1 <$> ts)
                           ) byLen
      listToMaybe $ HashSet.toList byGround

-- | For a given constructor to mode association and an applicative term,
-- computes modes of arguments of the head variable or constructor of the term.
argumentModes :: ModeAssoc -> Term1 -> [Mode]
argumentModes _  (Var _)    = []
argumentModes ma (Fun c ts) = matchModes ma c ts

-- | @initialTree n g@ is the initial "Tree Occ" for a logic program with @n@
-- clauses and a goal @g@.
initialTree :: Int -> ModeAssoc -> Goal1 -> ONode Occ
initialTree n ma (Go ts) =
  ONode $ (\(i,t) ->
            let mods = argumentModes ma t in
            ANode Occ { oTerm = t
                      , oMods = mods
                      , oPos = [i]
                      , oTodo = firstN n
                      , oVars = modedVarsTerm t mods}
                   mempty
          )
       <$> zip [0..] ts

firstN :: Int -> IntSet
firstN n = IntSet.fromAscList [0..n-1]

-- | "True" iff the tree doesn't have ground and-nodes that have no successors,
-- that is, such leaves that do not unify with any of the logic program clause
-- heads, and therefore a tree with such leaves is failed.
goodExtensionONode :: ONode Occ -> Bool
goodExtensionONode (ONode ts) = all (== True) (goodExtensionANode <$> ts)

goodExtensionANode :: ANode Occ -> Bool
goodExtensionANode (ANode Occ{oTerm = t} its)
  | IntSet.null (varsTerm1 t) && HashMap.null its = False
  | otherwise = all (== True) (goodExtensionONode <$> HashMap.elems its)

-- | A possibly infinite list of sets of trees where each set is a generation of
-- trees corresponding to a step in the incremental term matching of the goal
-- against the logic program.
derivation :: Program1 -> ModeAssoc -> Goal1 -> [HashSet (ONode Occ)]
derivation pr ma = takeUntil fin . iterate grow . good .
                   HashSet.singleton . extend . initialTree (length (unPr pr)) ma
  where
    extend t = growByMatchONode (liftedP t) ma t
    grow = foldr (\t -> (flip unionModEquiv)
                        (good $ extend `HashSet.map` growByMgu (liftedP t) ma t))
                 HashSet.empty
    good = HashSet.filter goodExtensionONode
    liftedP t = Pr $ liftVarsClause ((+1) <$> maxVarONode t) <$> unPr pr
    fin ts    = ts == HashSet.empty
                || any finalONode ts

-- | Finality check.
finalONode :: ONode Occ -> Bool
finalONode (ONode ts) = all (== True) (finalANode <$> ts)

finalANode :: ANode Occ -> Bool
finalANode (ANode Occ{oVars = vs} _) =
  IntMap.null $ IntMap.filter unevaluated vs
    where
      unevaluated (M Output Eager) = True
      unevaluated (M Input Lazy)   = True
      unevaluated _                = False

-- | @takeUntil p l@ returns the empty list if @l@ is empty, or otherwise the
-- prefix @m = as ++ [a]@ of @l@ such that
--
-- - @all p as@,
-- - @not (p a)@.
--
takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil _ []                 = []
takeUntil p (x:xs) | not (p x) = x : takeUntil p xs
                   | otherwise = [x]
