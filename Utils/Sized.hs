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

-- | Defines the Sized class, for things that have a notion of size

module Utils.Sized where

import Data.List

------------------------------------------------------------
-- * Sized class
------------------------------------------------------------

class Sized a where
  size :: (Num t) => a -> t

instance Sized a => Sized (Maybe a) where
  size = maybe 0 size

instance Sized [a] where
  size = genericLength
