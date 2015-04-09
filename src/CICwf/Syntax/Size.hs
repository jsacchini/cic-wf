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

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Sizes and annotations.

module CICwf.Syntax.Size where

-- import Text.PrettyPrint

-- import Data.Function
-- import Data.Functor

-- import CICwf.Utils.Misc
-- import CICwf.Utils.Pretty

-- ------------------------------------------------------------
-- -- * Size (or stage) variables
-- ------------------------------------------------------------

-- newtype StageVar = StageVar Integer
--                    deriving(Eq, Enum, Num)

-- instance Show StageVar where
--   show (StageVar x) = show x

-- instance Pretty StageVar where
--   prettyPrint (StageVar x) = integer x

-- -- | inftyStageVar is a special StageVar denoting infinity
-- --   It is used in the constraint solving algorithm
-- inftyStageVar :: StageVar
-- inftyStageVar = StageVar 0

-- ------------------------------------------------------------
-- -- * Sizes
-- ------------------------------------------------------------

-- data Size =
--   Svar StageVar      -- ^ Size variables
--   | Hat Size         -- ^ Successor size
--   | Infty            -- ^ Infinity


-- instance Eq Size where
--   (==) = (==) `on` normalize

-- instance Pretty Size where
--   prettyPrint s =
--     case normalize s of
--       Just (v, n) -> text $ "a" ++ show v ++ if n > 0 then "^" ++ show n else ""
--       Nothing     -> text "oo"

-- instance Show Size where
--   show = show . prettyPrint


-- -- | 'base' is only defined for sizes that have a variable at the bottom.
-- base :: Size -> Maybe StageVar
-- base (Svar n) = Just n
-- base (Hat s) = base s
-- base Infty    = Nothing


-- -- | Returns the number of 'Hat' applied to a variable or 'Infty'.
-- numHat :: Size -> Int
-- numHat (Svar _) = 0
-- numHat (Hat s) = numHat s + 1
-- numHat Infty    = 0

-- -- | Size normalization
-- --   The relation between 'normalize', 'base' and 'numHat' is the following:
-- --
-- --   base s = Just n    ==>  normalize s = Just (n, numHat s)
-- --
-- --   base s = Nothing   ==>  normalize s = Nothing

-- normalize :: Size -> Maybe (StageVar, Int)
-- normalize (Svar n) = Just (n, 0)
-- normalize (Hat s) = appSnd (+1) <$> normalize s
-- normalize Infty    = Nothing


-- ------------------------------------------------------------
-- -- * Size annotations for (co-)inductive types
-- ------------------------------------------------------------

-- -- data Annot =
-- --   Empty               -- ^ No annotation (for bare terms);
-- --   | Star              -- ^ For position types (in definition of (co-)fixpoints;
-- --   | Size Size         -- ^ An actual size annotation.


-- -- instance Eq Annot where
-- --   Empty    == Empty    = True
-- --   Star     == Star     = True
-- --   Size s1  == Size s2  = s1 == s2
-- --   _        == _        = False

-- -- instance Pretty Annot where
-- --   prettyPrint Empty = text ""
-- --   prettyPrint Star  = text "*"
-- --   prettyPrint (Size s) = prettyPrint s

-- -- instance Show Annot where
-- --   show = show . prettyPrint
