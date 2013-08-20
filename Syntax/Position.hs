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

-- | Positions and ranges are used to print information about where errors occur

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances
  #-}

module Syntax.Position where

import Text.PrettyPrint as PP

import Utils.Pretty
import Utils.Value


data Position = Pn { posFile :: FilePath,
                     posLine :: Int,
                     posCol :: Int }
                deriving(Eq)

data Range = Range { rStart, rEnd :: !Position }
           | NoRange
           deriving(Eq)

data Ranged a = Ranged { rangeTag :: Range,
                         rangedValue :: a }
                deriving(Show, Eq)

instance HasValue (Ranged a) a where
  value = rangedValue

instance Functor Ranged where
  fmap f x = x { rangedValue = f (rangedValue x) }

mkRanged :: Range -> a -> Ranged a
mkRanged = Ranged

class HasRange a where
  range :: a -> Range

instance HasRange a => HasRange (Ranged a) where
  range = range . rangeTag

instance Show Position where
   show (Pn path line col) = concat [path, ":", show line, ":", show col]
    -- show _ = ""

instance Show Range where
    show (Range start end) = concat [-- posFile start,
                                     ":",
                                     show (posLine start), ":",
                                     show (posCol start), "-",
                                     show (posLine end), ":",
                                     show (posCol end)]
    show NoRange = "-:-"

instance Pretty Range where
    prettyPrint (Range start end) = text $ concat [posFile start,
                                     ":",
                                     show (posLine start), ":",
                                     show (posCol start), "-",
                                     show (posLine end), ":",
                                     show (posCol end)]

instance HasRange Position where
  range p = Range p p

instance HasRange Range where
  range r = r

instance HasRange a => HasRange [a] where
  range [] = noRange
  range [x] = range x
  range (x:y:ys) = fuseRange (range x) (range (y:ys))

instance HasRange a => HasRange (Maybe a) where
  range = maybe NoRange range

class HasRange t => SetRange t where
  setRange :: Range -> t -> t

instance SetRange Range where
  setRange = const

noPosFile :: FilePath -> Position
noPosFile f = Pn f 0 0

noPos :: Position
noPos = noPosFile ""

initPosFile :: FilePath -> Position
initPosFile f = Pn f 1 1

initPos :: Position
initPos = initPosFile ""

noRange :: Range
noRange = NoRange -- Range noPos noPos

noRangeFile :: FilePath -> Range
noRangeFile f = Range (noPosFile f) (noPosFile f)


movePos :: Position -> Char -> Position
movePos (Pn f l c) '\t' = Pn f l (((c+7) `div` 8)*8+1)
movePos (Pn f l _) '\n' = Pn f (l+1) 1
movePos (Pn f l c) _    = Pn f l (c+1)

advancePos :: Position -> Int -> Position
advancePos (Pn f l c) n = Pn f l (c + n)

mkRangeLen :: Position -> Int -> Range
mkRangeLen pos n = Range pos (advancePos pos n)

-- Combines two ranges
-- Assumes that the first range is to the left of the second
fuseRange :: (HasRange a, HasRange b) => a -> b -> Range
fuseRange x y = case (range x, range y) of
                  (Range posl _ , Range _ posr ) -> Range posl posr
                  (NoRange      , r@(Range _ _)) -> r
                  (r@(Range _ _), NoRange      ) -> r
                  (_            , _            ) -> NoRange

-- fuseRanges only works in non-empty lists
fuseRanges :: HasRange a => [a] -> Range
fuseRanges = foldr1 fuseRange . map range
