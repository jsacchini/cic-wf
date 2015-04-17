{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

-- | Constraint sets.

module CICwf.TypeChecking.Constraints
       ( EdgeLabel
       , Constraint
       , ConstraintSet
       , empty
       , addNode
       , addNodes
       , delNode
       , delNodes
       , listNodes
       , labNodes
       , addConstraints
       , findNegCycle
       , upward
       , downward
       , toList
       , lab
       , shortestPath
       , CSet ) where

import           Data.Map                   (Map)
import qualified Data.Map                   as Map

import qualified Data.Graph.Inductive       as G
import qualified Data.Graph.Inductive       as GI
-- import Data.Graph.Inductive.PatriciaTree as GI
import qualified Data.Graph.Inductive.Query as GQ
import qualified Data.Graph.Inductive.Internal.Heap as GH
import qualified Data.Graph.Inductive.Internal.RootPath as GR

-- | A node is represented by Int. Zero represents the node labeled by Infty
--   TODO: record range information on the nodes, to identify in which part of the
--   code it was introduced. Could be used to give good error messages when a
--   fixpoint is not well-typed
-- type Node = G.LNode ()

-- | A stage constraint of the form a1^n1 <= a2^n2 is represented by an egde of the
--   form  (a1, a2, n2 - n1).
--
--   A sort constraint of the form Type(i) <= Type(j) is represented by (i, j, 0)
--   while a constraint of the form Type(i) < Type(j) is represented by (i, j, -1)
type EdgeLabel = Int

type Constraint a = (a, a, EdgeLabel) -- G.LEdge EdgeLabel

class Enum a => ConstraintSet c a b where
  -- defaultLabel :: b
  empty          :: c a b
  addNode        :: a              -> b -> c a b -> c a b
  addNodes       :: [(a, b)]       -> c a b -> c a b
  delNode        :: a              -> c a b -> c a b
  delNodes       :: [a]            -> c a b -> c a b
  listNodes      :: c a b          -> [a]
  labNodes       :: c a b          -> [(a, b)]
  addConstraints :: [Constraint a] -> c a b -> c a b
  findNegCycle   :: a              -> c a b -> [a]
  upward         :: c a b          -> [a] -> [a]
  downward       :: c a b          -> [a] -> [a]
  toList         :: c a b          -> [Constraint a]
  lab            :: c a b          -> a -> Maybe b
  shortestPath   :: c a b          -> a -> a -> Maybe Int

  addNodes xs c = foldr (uncurry addNode) c xs
  delNodes xs c = foldr delNode c xs


newtype CSet a b = CSet (GI.Gr b EdgeLabel)
                   deriving(Show)

instance Enum a => ConstraintSet CSet a b where
  empty = CSet G.empty

  addNode k lab (CSet g) = CSet $ G.insNode (mkNode k) g
    where mkNode k = (fromEnum k, lab)

  delNode k (CSet g) = CSet $ G.delNode (fromEnum k) g

  listNodes (CSet g) = map toEnum $ G.nodes g

  labNodes (CSet g) = map (\(x, y) -> (toEnum x, y)) $ G.labNodes g

  addConstraints cts (CSet g) = CSet $ GI.insEdges labCts g
    where
      labCts = map (\ (x, y, k) -> (fromEnum x, fromEnum y, k)) cts

  upward (CSet gr) = map toEnum . upF [] . map fromEnum
    where upF vs [] = vs
          upF vs (x:xs) | x `elem` vs = upF vs xs
                        | otherwise   = upF (x:vs) (GI.suc gr x ++ xs)

  downward (CSet gr) = map toEnum . downF [] . map fromEnum
    where downF vs [] = vs
          downF vs (x:xs) | x `elem` vs = downF vs xs
                          | otherwise   = downF (x:vs) (GI.pre gr x ++ xs)

  findNegCycle v g@(CSet g0) = map toEnum $ foldr (\x r -> edgeCheck x bfmap ++ r) [] (GI.labEdges g0)
    where
      bfmap = bellmanFord v g
      -- check cycle on updated map
      edgeCheck :: (Int, Int, Int) -> BFMap -> [Int]
      edgeCheck (n1, n2, l) m
        | snd (m Map.! n1) `dP` DistVal l < snd (m Map.! n2) =
          [n1]
        | otherwise = []

  toList (CSet gr) = map mkConstr (GI.labEdges gr)
                     where mkConstr (x, y, k) = (toEnum x, toEnum y, k)

  lab (CSet g) = GI.lab g . fromEnum

  shortestPath g n1 n2 =
    case bfmap Map.! fromEnum n2 of
      (_, DistVal k) -> Just k
      (_, DistInfty) -> Nothing
    where
      bfmap = bellmanFord n1 g

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


bellmanFord :: (Enum a) => a -> CSet a b -> BFMap
bellmanFord src_ (CSet g) = bfmap -- map toEnum $ foldr (\x r -> edgeCheck x bfmap ++ r) [] (GI.labEdges g)
  where
    src = fromEnum src_
    ns :: [Int]
    ns = GI.nodes g
    init :: BFMap
    init = sUpd Nothing (DistVal 0) src $
           foldr (uncurry Map.insert) Map.empty (zip ns (repeat (Nothing, DistInfty)))
    sUpd :: Maybe Pred -> Distance -> Int -> BFMap -> BFMap
    sUpd pred dist k = Map.update (const (Just (pred, dist))) k
    edgeUpd :: (Int, Int, EdgeLabel) -> BFMap -> BFMap
    edgeUpd (n1, n2, lab) m
      | snd (m Map.! n1) `dP` (DistVal lab) < snd (m Map.! n2) =
        sUpd (Just n1) (snd (m Map.! n1) `dP` (DistVal lab)) n2 m
      | otherwise = m

    edgeLoop :: BFMap -> BFMap
    edgeLoop m = foldr edgeUpd m (GI.labEdges g)
    repF :: Int -> (a -> a) -> a -> a
    repF 0 _ x = x
    repF k f x = repF (k-1) f (f x)

    bfmap :: BFMap
    bfmap = repF (length ns - 1) edgeLoop init

    -- check cycle on updated map
    edgeCheck :: (Int, Int, Int) -> BFMap -> [Int]
    edgeCheck (n1, n2, l) m
      | snd (m Map.! n1) `dP` DistVal l < snd (m Map.! n2) =
        [n1]
      | otherwise = []
