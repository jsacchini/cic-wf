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

module CICminus.TypeChecking.RecCheck (recCheck) where

import           Data.List
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe

import qualified Data.Graph.Inductive       as G
import qualified Data.Graph.Inductive       as GI
-- import Data.Graph.Inductive.PatriciaTree as GI
import qualified Data.Graph.Inductive.Query as GQ

import           CICminus.Syntax.Internal
import           CICminus.Syntax.Position
-- import           CICminus.Syntax.Size
import           CICminus.TypeChecking.Constraints
import           CICminus.TypeChecking.TCM

-- type CStage = CSet StageNode Range
type Node = (StageNode, Range)

-- add many constraints
addManyC :: SizeConstraint -> StageNode -> [StageNode] -> SizeConstraint
addManyC (SizeConstraint gr) x ys = SizeConstraint $ addConstraints con gr
  where con = map (\y -> (x, y, 0)) ys


-- RecCheck
-- | 'recCheck alpha V* V≠ C'
recCheck :: StageNode -> [StageNode] -> [StageNode] -> SizeConstraint ->
            Either SizeConstraint [StageNode]
recCheck alpha vStar vNeq c = result
  where
    -- Step 1
    si = downward (unSC c) vStar

    -- Step 2
    c1 = addManyC c alpha si

    -- Step 3
    -- Compute upward closure of a cycle. Returns [] if no cycle exists
    upwardCycle :: SizeConstraint -> [Node]
    upwardCycle (SizeConstraint gr) =
      labs (upward gr $ nub $ concatMap (flip findNegCycle gr) ns)
      where
        ns :: [StageNode]
        ns = listNodes gr
        labs :: [StageNode] -> [Node]
        labs = map (\x -> (x, fromJust (lab gr x)))

    -- upward gr (findCycle gr)
    -- Remove edges and add infinite constraints
    addInfty :: SizeConstraint -> [Node] -> SizeConstraint
    addInfty (SizeConstraint gr) beta =
      addManyC (SizeConstraint (addNodes beta (delNodes betaNodes gr))) InftyNode betaNodes
      where
        betaNodes = map fst beta

    c2 = c2F c1
      where
        c2F :: SizeConstraint -> SizeConstraint
        c2F gr =
          case upwardCycle gr of
            beta@(_:_) -> c2F (addInfty gr beta)
            []         -> gr

    -- Step 4
    siSub = upward (unSC c2) si

    -- Step 5
    sNegi = upward (unSC c2) vNeq

    -- Step 6
    sInt = intersect sNegi siSub
    c3 = addManyC c2 InftyNode sInt

    -- Step 7
    sInfty = upward (unSC c3) [InftyNode]

    -- Step 8
    sRes = sInfty `intersect` si
    result | sRes == [] = Left c3
           | otherwise  = Right sRes
