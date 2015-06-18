module CoALP.Resolution where

import Prelude hiding (all, any, foldr, concatMap, sequence_)

import CoALP.Term
import CoALP.Clause
import CoALP.Subst
import CoALP.Tree

import Control.Applicative
import Data.Array ((!), (//))
import qualified Data.Array as Array
import Data.Foldable
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

maxVarTree :: TreeOper1 -> Maybe Int
maxVarTree = foldr (max . foldr (max . Just) Nothing) Nothing

unifSubtrees :: Program1 -> TreeOper1 -> [(Transition, TreeOper1)]
unifSubtrees p t = go t []
  where
    nVars = (+ 1) <$> maxVarTree t
    go :: TreeOper1 -> Path -> [(Transition, TreeOper1)]
    go (NodeOper a b) prefix =
      (\(i, oper) ->
        case oper of
         Right (Just ts)  -> (\(j, u) -> go u (prefix ++ [i, j])
                             ) `concatMap` (zip [0..] ts)
         Left ToBeUnified -> [(Transition w ms, grow w $ unifyTerms t)]
           where
             w = prefix ++ [i]
             ms = clHead c `mguMaybe` a
             c = liftVarsClause nVars $ (program p)!i

             unifyTerms
               | isNothing ms = id
               | otherwise = fmap (>>= subst (fromJust ms))

             grow :: Path -> TreeOper1 -> TreeOper1
             grow (k:l:u) (NodeOper a0 b0) =
               NodeOper a0 $ b0 // [(k,
                                     case b0!k of
                                      Right (Just tbs) ->
                                        Right $ Just $
                                        take l tbs ++ grow u (tbs!!l) :
                                        drop (l+1) tbs
                                      _ -> error "unifSubtrees: invalid path"
                                    )]
             grow [k] (NodeOper a0 b0) = NodeOper a0 $ b0 // [(k, o)]
               where
                 o :: Oper [TreeOper1]
                 o | isNothing ms = Right Nothing
                   | otherwise    = Right $ Just tbs
                 tbs = initTree (Array.bounds $ program p) <$>
                       (>>= subst (fromJust ms)) <$> clBody c
             grow _ _ = error "unifSubtrees: grow error"

         _ -> []
      ) `concatMap` (Array.assocs b)

runResolution :: Program1 -> Term1 ->
                 (Either (Halt TreeOper1) (), Derivation TreeOper1)
runResolution p a = runDerivation (Array.bounds $ program p) a f h
  where
    f = unifSubtrees p . matchTree p
    h t = if successful t then Just t else Nothing

successful :: TreeOper1 -> Bool
successful = any hasSuccess . Array.elems . nodeBundleOper
  where
    hasSuccess (Right (Just ts)) = all final ts || any successful ts
    hasSuccess _                 = False

final :: TreeOper1 -> Bool
final = all finalB . Array.elems . nodeBundleOper
  where
    finalB (Right (Just ts)) = all final ts
    finalB (Right Nothing)   = True
    finalB _                 = False
