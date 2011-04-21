{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, PackageImports,
  FlexibleInstances, UndecidableInstances #-}

-- | Not very interesting now...

module Syntax.Common where

import Text.PrettyPrint

import Syntax.Position
import Utils.Pretty


-- | Identifiers
newtype Name = Id { unName :: String }
               deriving(Eq, Ord)

instance Show Name where
  show (Id s) = "Id " ++ s

noName :: Name
noName = Id ""

isNull :: Name -> Bool
isNull (Id "") = True
isNull _       = False

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


-- | Polarities
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
