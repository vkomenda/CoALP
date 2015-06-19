module CoALP.Resolution where

import Prelude hiding (all, any, foldr, concatMap, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst
import CoALP.Tree

import Control.Applicative
import Control.Arrow
import Data.Array ((!), (//))
import qualified Data.Array as Array
import Data.Foldable
import Data.List (partition)
import Data.Maybe

toBeUnified :: TreeOper1 -> Path -> [Path]
toBeUnified (NodeOper _ b) prefix =
  (\(i, oper) ->
    case oper of
     Left ToBeUnified -> [prefix ++ [i]]
     Right (Just ts)  -> (\(j, t) ->
                           toBeUnified t (prefix ++ [i, j])
                         ) `concatMap` (zip [0..] ts)
     _ -> []
  ) `concatMap` (Array.assocs b)

mguTransitions :: Program1 -> TreeOper1 -> [(Transition, TreeOper1)]
mguTransitions p t = growSuccessful $ failedAndSuccessful $ atBoundary [] t
  where
    growSuccessful :: ([Path], [(Path, Subst1)]) -> [(Transition, TreeOper1)]
    growSuccessful (pts, trs) =
      (\(w, s) ->
        ( Transition w s
        , grow (Just s) w $ (>>= subst s) <$> noMgu pts)
      ) <$> trs

    noMgu :: [Path] -> TreeOper1
    noMgu = foldr (grow Nothing) t

    failedAndSuccessful :: [(a, Maybe b)] -> ([a], [(a, b)])
    failedAndSuccessful =
      (map fst *** map (id *** fromJust)) . partition (isNothing . snd)

    atBoundary :: Path -> TreeOper1 -> [(Path, Maybe Subst1)]
    atBoundary prefix (NodeOper a b) =
      (\(i, oper) ->
        case oper of
         Right (Just ts)  -> (\(j, u) -> atBoundary (prefix ++ [i, j]) u
                             ) `concatMap` (zip [0..] ts)
         Left ToBeUnified -> [( prefix ++ [i]
                              , clHead (liftedClause i) `mguMaybe` a)]
         _ -> []
      ) `concatMap` (Array.assocs b)

    grow :: Maybe Subst1 -> Path -> TreeOper1 -> TreeOper1
    grow ms (i:k:u) (NodeOper a0 b0) =
      NodeOper a0 $ b0 // [(i,
                            case b0!i of
                             Right (Just tbs) ->
                               Right $ Just $
                               take k tbs ++ grow ms u (tbs!!k) :
                               drop (k+1) tbs
                             _ -> error "matchSubtrees: invalid path"
                                  -- TODO: return
                           )]
    grow ms [i] (NodeOper a0 b0) = NodeOper a0 $ b0 // [(i, o)]
      where
        o :: Oper [TreeOper1]
        o | isNothing ms = Right Nothing
          | otherwise    = Right $ Just tbs
        tbs = initTree (Array.bounds $ program p) <$>
              (>>= subst (fromJust ms)) <$> clBody (liftedClause i)
    grow _ _ _ = error "matchSubtrees: grow error"

    liftedClause i = liftVarsClause nVars $ (program p)!i
    nVars = (+ 1) <$> maxVarTree t

runResolution :: Program1 -> Term1 ->
                 (Either (Halt TreeOper1) (), Derivation TreeOper1)
runResolution p a = runDerivation (Array.bounds $ program p) a f h
  where
    f = mguTransitions p . matchTree p
    h t = if successful t then Just t else Nothing

successful :: TreeOper1 -> Bool
successful = any hasSuccess . Array.elems . nodeBundleOper
  where
    hasSuccess (Right (Just ts)) = all final ts || all successful ts
    hasSuccess _                 = False

final :: TreeOper1 -> Bool
final = all finalB . Array.elems . nodeBundleOper
  where
    finalB (Right (Just ts)) = all final ts
    finalB (Right Nothing)   = True
    finalB _                 = False
