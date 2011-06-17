{-# LANGUAGE CPP #-}

module Kernel.Constraints where

import Data.Maybe

import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive as GI
-- import Data.Graph.Inductive.PatriciaTree as GI

import Syntax.Size

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

type Constraint = G.LEdge EdgeLabel


type ConstraintSet = GI.Gr () EdgeLabel

-- | An empty set of constraints contains at least the node zero
emptyConstraints :: ConstraintSet
emptyConstraints = G.insNode (0, ()) G.empty


(<<=) :: Annot -> Annot -> [Constraint]
(<<=) (Size s1) (Size s2) = [(a1, a2, LEQ (n2 - n1))]
  where mapInfty = fromMaybe (0, 0)
        (a1, n1) = mapInfty $ normalize s1
        (a2, n2) = mapInfty $ normalize s2
(<<=) Empty Empty = []
(<<=) _ _ = []
-- (<<=) a1 a2 = error $ "comparing sizes " ++ show a1 ++ " <<=> " ++ show a2
-- (<<=) _ _ = __IMPOSSIBLE__

(<<>>) :: Annot -> Annot -> [Constraint]
(<<>>) a1 a2 = a1 <<= a2 ++ a2 <<= a1
