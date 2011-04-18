{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, PackageImports,
  FlexibleInstances, UndecidableInstances #-}

-- | Not very interesting now...

module Syntax.Common where

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
  show Neut = "o"
