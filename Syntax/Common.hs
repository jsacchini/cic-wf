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

-- | Some common datatypes that are used by both "Syntax.Abstract" and
--   "Syntax.Internal"

module Syntax.Common where

import qualified Data.Foldable as Fold
import Data.Maybe
import Data.Monoid hiding ((<>))

import Text.PrettyPrint

import Utils.Pretty
import Utils.Sized


------------------------------------------------------------
-- * Identifiers
------------------------------------------------------------

newtype Name = Id { unName :: String }
               deriving(Eq, Ord)

instance Show Name where
  show (Id xs) | null xs = "_"
               | otherwise = xs

noName :: Name
noName = Id ""

isNull :: Name -> Bool
isNull (Id "") = True
isNull _       = False

mkName :: String -> Name
mkName = Id

instance Pretty Name where
  prettyPrint (Id xs) | null xs   = text "_"
                      | otherwise = text xs


-- | Used for bindings
class HasNames a where
  getNames :: a -> [Name]

instance HasNames a => HasNames [a] where
  getNames = concatMap getNames

instance HasNames Name where
  getNames n = [n]

instance HasNames a => HasNames (Maybe a) where
  getNames = maybe [] getNames

class Rename a where
  rename :: a -> [Name] -> a

------------------------------------------------------------
-- * Polarities
------------------------------------------------------------

data Polarity = Pos
              | Neg
              | SPos
              | Neut

instance Show Polarity where
  show Pos  = "+"
  show Neg  = "-"
  show SPos = "++"
  show Neut = "@"

instance Pretty Polarity where
  prettyPrint = text . show

data Polarized a = Pol { polarity :: Polarity,
                         unPol :: a }
                   deriving(Show)

------------------------------------------------------------
-- * Inductive kind (data/codata, fixpoint/cofixpoint)
------------------------------------------------------------

data InductiveKind = I | CoI
                   deriving(Eq,Show)

------------------------------------------------------------
-- * Contexts
------------------------------------------------------------

data Ctx a = EmptyCtx
           | ExtendCtx a (Ctx a)

instance Functor Ctx where
  fmap f EmptyCtx = EmptyCtx
  fmap f (ExtendCtx x c) = ExtendCtx (f x) (fmap f c)

instance Fold.Foldable Ctx where
  foldr f r EmptyCtx = r
  foldr f r (ExtendCtx x c) = f x (Fold.foldr f r c)

  foldMap _ EmptyCtx = mempty
  foldMap f (ExtendCtx b c) = f b `mappend` Fold.foldMap f c


instance HasNames a => HasNames (Ctx a) where
  getNames EmptyCtx = []
  getNames (ExtendCtx b c) = getNames b ++ getNames c

fromList :: [a] -> Ctx a
fromList = foldr ExtendCtx EmptyCtx

(+:) :: Ctx a -> Ctx a -> Ctx a
(+:) = flip $ Fold.foldr ExtendCtx

empCtx :: Ctx a
empCtx = EmptyCtx

instance Sized (Ctx a) where
  size = Fold.foldr (\_ k -> k + 1) 0

ctxLen :: Ctx a -> Int
ctxLen = size

(<|) :: a -> Ctx a -> Ctx a
(<|) = ExtendCtx

singleCtx :: a -> Ctx a
singleCtx b = b <| empCtx

(|>) :: Ctx a -> a -> Ctx a
(|>) c1 b = c1 +: singleCtx b

ctxSplit :: Ctx a -> (a, Ctx a)
ctxSplit (ExtendCtx h t) = (h, t)

ctxReverse :: Ctx a -> Ctx a
ctxReverse = Fold.foldr (\c cs -> cs |> c) EmptyCtx

ctxSplitAt :: Int -> Ctx a -> (Ctx a, Ctx a)
ctxSplitAt 0 ctx = (empCtx, ctx)
ctxSplitAt k ctx =
  case tail of
    EmptyCtx -> (head, tail)
    ExtendCtx b ctx' -> (head |> b, ctx')
  where (head, tail) = ctxSplitAt (k-1) ctx

instance Eq a => Eq (Ctx a) where
  EmptyCtx == EmptyCtx = True
  (ExtendCtx b1 c1) == (ExtendCtx b2 c2) = b1 == b2 && c1 == c2
  _ == _ = False

