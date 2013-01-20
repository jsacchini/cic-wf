{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

module Kernel.RecCheck (recCheck) where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Graph.Inductive as G
import qualified Data.Graph.Inductive as GI
-- import Data.Graph.Inductive.PatriciaTree as GI
import qualified Data.Graph.Inductive.Query as GQ

import Kernel.Constraints
import Syntax.Size

type CStage = CSet StageVar

-- add many constraints
addManyC :: CStage -> StageVar -> [StageVar] -> CStage
addManyC gr x ys = addConstraints con gr
  where con = map (\y -> (x, y, 0)) ys


-- RecCheck
-- | 'recCheck alpha V* V≠ C'
recCheck :: StageVar -> [StageVar] -> [StageVar] -> CStage -> Either CStage [StageVar]
recCheck alpha vStar vNeq c = result
  where -- Step 1
        si = downward c vStar
        -- Step 2
        c1 = addManyC c alpha si
        -- Step 3
        -- Compute upward closure of a cycle. Returns [] if no cycle exists
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        --   upward gr (findCycle gr)
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) inftyStageVar beta
            --where beta' = map (\x -> (x, ())) beta
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

gr0 :: CSet Int
gr0 = addNodes [0..7] empty

mkEdge (n1, n2, k) = (n1, n2, k)
gr1 = addConstraints
                  (map mkEdge [(1,3,-1),
                               (3,4,1),
                               (4,1,0),
                               (2,7,0),
                               (5,2,0),
                               (6,5,-1),
                               (7,5,-1)]
                  ) gr0

gr2 = addConstraints
                  (map mkEdge [(1,3,-1),
                               (2,5,0),
                               (3,4,1),
                               (4,7,0),
                               (5,2,0),
                               (6,5,-1),
                               (7,1,-1)]
                  ) gr1


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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) inftyStageVar beta
            -- where beta' = map (\x -> (x, ())) beta
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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) 0 beta
            --where beta' = map (\x -> (x, ())) beta
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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) 0 beta
            --where beta' = map (\x -> (x, ())) beta
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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) 0 beta
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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) 0 beta
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
        upwardCycle gr = upward gr $ nub $ concatMap (flip findNegCycle gr) ns
                         where ns :: [StageVar]
                               ns = listNodes gr
        -- Remove edges and add infinite constraints
        addInfty gr beta =
          addManyC (addNodes beta (delNodes beta gr)) 0 beta
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

