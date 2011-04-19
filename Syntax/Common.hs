{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, PackageImports,
  FlexibleInstances, UndecidableInstances #-}

-- | Not very interesting now...

module Syntax.Common where

import Text.PrettyPrint

import Utils.Pretty


-- | Identifiers
type Name = String

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
