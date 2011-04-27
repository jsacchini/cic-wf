module Kernel.Constraints where

import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive as GI
-- import Data.Graph.Inductive.PatriciaTree as GI


-- | A node is represented by Int. Zero represents the node labeled by Infty
type Node = G.LNode ()

-- | A constraint of the form a1^n1 <= a2^n2 is represented by an egde of the
--   form  (a1, a2, LEQ (n2 - n1)).
--
--   We also allow to represent assignments of nodes. If a1 = a2^n, then we have
--   an edge of the form  (a1, a2, Same n)
data EdgeLabel = LEQ Int
               | Same Int
               deriving(Show)

type Edge = G.LEdge EdgeLabel

type Constraints = GI.Gr () EdgeLabel

-- | An empty set of constraints contains at least the node zero
emptyConstraints :: Constraints
emptyConstraints = G.insNode (0, ()) G.empty
