{-# LANGUAGE CPP #-}

module Kernel.Constraints where

import Data.List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive as GI
-- import Data.Graph.Inductive.PatriciaTree as GI
import qualified Data.Graph.Inductive.Query as GQ

import Syntax.Size

import Utils.Misc

#include "../undefined.h"
import Utils.Impossible

-- | A node is represented by Int. Zero represents the node labeled by Infty
type Node = G.LNode ()

-- | A constraint of the form a1^n1 <= a2^n2 is represented by an egde of the
--   form  (a1, a2, LEQ (n2 - n1)).
--
--   We also allow to represent assignments of nodes. If a1^n1 = a2^n2, then
--   we have an edge of the form  (a1, a2, Same (n2 - n1)).
--
--   The edges of the form (Same _) should form an DAG
data EdgeLabel = LEQ Int
               | Same Int
               deriving(Show)

edgeVal :: EdgeLabel -> Int
edgeVal (LEQ k) = k
edgeVal (Same k) = k

type Constraint = G.LEdge EdgeLabel


-- TODO: record range information on the nodes, to identify in which part of the
-- code it was introduced. Could be used to give good error messages when a
-- fixpoint is not well-typed
type ConstraintSet = GI.Gr () EdgeLabel

-- | An empty set of constraints contains at least the node zero
emptyConstraints :: ConstraintSet
emptyConstraints = G.insNode (0, ()) G.empty


validConstraint :: Constraint -> Bool
validConstraint (n1, n2, d) = (n1 /= 0 || n2 /= 0) && (n1 == n2 ==> val d /= 0)
  where val (LEQ k) = k
        val (Same k) = k

(<<=) :: Annot -> Annot -> [Constraint]
(<<=) (Size s1) (Size s2) = filter validConstraint [(a1, a2, LEQ (n2 - n1))]
  where mapInfty = fromMaybe (0, 0)
        (a1, n1) = mapInfty $ normalize s1
        (a2, n2) = mapInfty $ normalize s2
(<<=) _ _ = __IMPOSSIBLE__
-- (<<=) a1 a2 = error $ "comparing sizes " ++ show a1 ++ " <<=> " ++ show a2
-- (<<=) _ _ = __IMPOSSIBLE__

(<<>>) :: Annot -> Annot -> [Constraint]
(<<>>) a1 a2 = a1 <<= a2 ++ a2 <<= a1


-- Algorithms to compute RecCheck... everything is very slow

-- upward closure of a set
upward :: ConstraintSet -> [Int] -> [Int]
upward gr = upF []
  where upF vs [] = vs
        upF vs (x:xs) | x `elem` vs = upF vs xs
                      | otherwise   = upF (x:vs) (GI.suc gr x ++ xs)

-- downward closure of a set
downward :: ConstraintSet -> [Int] -> [Int]
downward gr = downF []
  where downF vs [] = vs
        downF vs (x:xs) | x `elem` vs = downF vs xs
                        | otherwise   = downF (x:vs) (GI.pre gr x ++ xs)

-- cycle... very very slow
findCycle :: ConstraintSet -> [Int]
findCycle gr = visited [] (GI.nodes gr)
  where visited _ [] = []
        visited vs (x:xs) | x `elem` vs = [x]
                          | otherwise   = visited (x:vs) ((xs \\ next) ++ next)
                                          where next = GI.suc gr x

-- Bellman-Ford
type Pred = Int
data Distance = DistVal Int | DistInfty
              deriving(Eq,Show)
type BFMap = Map Int (Maybe Pred, Distance)

instance Ord Distance where
  compare (DistVal n1) (DistVal n2) = n1 `compare` n2
  compare DistInfty (DistVal _) = GT
  compare (DistVal _) DistInfty = LT
  compare DistInfty DistInfty = EQ

dP :: Distance -> Distance -> Distance
dP (DistVal n1) (DistVal n2) = DistVal (n1 + n2)
dP _ _ = DistInfty

bellmanFord :: Int -> ConstraintSet -> [Int]
bellmanFord src g = foldr (\x r -> edgeCheck x updateMap ++ r) [] (GI.labEdges g)
  where ns :: [Int]
        ns = GI.nodes g
        init :: BFMap
        init = sUpd Nothing (DistVal 0) src $
               foldr (uncurry Map.insert) Map.empty (zip ns (repeat (Nothing, DistInfty)))
        sUpd :: Maybe Pred -> Distance -> Int -> BFMap -> BFMap
        sUpd pred dist k = Map.update (const (Just (pred, dist))) k
        edgeUpd :: (Int, Int, EdgeLabel) -> BFMap -> BFMap
        edgeUpd (n1, n2, lab) m
          | snd (m Map.! n1) `dP` (DistVal (edgeVal lab)) < snd (m Map.! n2) =
            sUpd (Just n1) (snd (m Map.! n1) `dP` (DistVal (edgeVal lab))) n2 m
          | otherwise = m
        edgeLoop m = foldr edgeUpd m (GI.labEdges g)
        repF :: Int -> (a -> a) -> a -> a
        repF 0 _ x = x
        repF k f x = repF (k-1) f (f x)

        updateMap :: BFMap
        updateMap = repF (length ns - 1) edgeLoop init

        -- check cycle on updated map
        edgeCheck (n1, n2, lab) m
          | snd (m Map.! n1) `dP` (DistVal (edgeVal lab)) < snd (m Map.! n2) =
            [n1]
          | otherwise = []


-- add many constraints
addManyC :: ConstraintSet -> Int -> [Int] -> ConstraintSet
addManyC gr x ys = foldr GI.insEdge gr (filter validConstraint con)
  where con = map (\y -> (x, y, LEQ 0)) ys


-- RecCheck
-- | 'recCheck alpha V* V≠ C'
recCheck :: Int -> [Int] -> [Int] -> ConstraintSet -> Either ConstraintSet [Int]
recCheck alpha vStar vNeq c = result
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        --   upward gr (findCycle gr)
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si
        -- Step 5
        sNegi = upward c2 vNeq
        -- Step 6
        sInt = intersect sNegi siSub
        c3 = addManyC c2 0 sInt
        -- Step 7
        sInfty = upward c3 [0]
        -- Step 8
        sRes = sInfty `intersect` si
        result | sRes == [] = Left c3
               | otherwise  = Right sRes

--- Testing recCheck

mkNode x = (x, ())

gr0 :: ConstraintSet
gr0 = GI.insNodes (map mkNode [0..7]) GI.empty

mkEdge (n1, n2, k) = (n1, n2, LEQ k)
gr1 = GI.insEdges (map mkEdge [(1,3,-1),
                               (3,4,1),
                               (4,1,0),
                               (2,7,0),
                               (5,2,0),
                               (6,5,-1),
                               (7,5,-1)]
                  ) gr0

gr2 = GI.insEdges (map mkEdge [(1,3,-1),
                               (2,5,0),
                               (3,4,1),
                               (4,7,0),
                               (5,2,0),
                               (6,5,-1),
                               (7,1,-1)]
                  ) gr0


try1 f = f 1 [1] ([2]) gr1
try2 f = f 1 [1] ([2]) gr2

step1 alpha vStar vNeq c = si
  where -- Step 1
        si = downward c vStar

step2 alpha vStar vNeq c = c1
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si

step3 alpha vStar vNeq c = c2
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr

step4 alpha vStar vNeq c = siSub
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si

step5 alpha vStar vNeq c = sNegi
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si
        -- Step 5
        sNegi = upward c2 vNeq

step6 alpha vStar vNeq c = c3
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si
        -- Step 5
        sNegi = upward c2 vNeq
        -- Step 6
        sInt = intersect sNegi siSub
        c3 = addManyC c2 0 sInt

step7 alpha vStar vNeq c = sInfty
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si
        -- Step 5
        sNegi = upward c2 vNeq
        -- Step 6
        sInt = intersect sNegi siSub
        c3 = addManyC c2 0 sInt
        -- Step 7
        sInfty = upward c3 [0]

step8 alpha vStar vNeq c = result
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip bellmanFord gr) ns
                         where ns :: [Int]
                               ns = GI.nodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (GI.insNodes beta' (GI.delNodes beta gr)) 0 beta
            where beta' = map (\x -> (x, ())) beta
        c2 = c2F c1
          where c2F gr = case upwardCycle gr of
                           beta@(_:_) -> c2F (addInfty gr beta)
                           []         -> gr
        -- Step 4
        siSub = upward c2 si
        -- Step 5
        sNegi = upward c2 vNeq
        -- Step 6
        sInt = intersect sNegi siSub
        c3 = addManyC c2 0 sInt
        -- Step 7
        sInfty = upward c3 [0]
        -- Step 8
        sRes = sInfty `intersect` si
        result | sRes == [] = Left c3
               | otherwise  = Right sRes
