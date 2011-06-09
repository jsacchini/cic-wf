-- | Some common datatypes that are used by both "Syntax.Abstract" and
--   "Syntax.Internal"

module Syntax.Common where

import Text.PrettyPrint

import Utils.Pretty


-- | Identifiers
newtype Name = Id { unName :: String }
               deriving(Eq, Ord)

instance Show Name where
  show = unName

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

instance HasNames a => HasNames (Maybe a) where
  getNames = maybe [] getNames

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

data Polarized a = Pol { polarity :: Polarity,
                         unPol :: a }
                   deriving(Show)

-- | Sorts

data Sort
    = Type Int
    | Prop
    deriving(Eq)

instance Show Sort where
  show Prop = "Prop"
  show (Type n) = "Type" ++ show n

instance Ord Sort where
  compare Prop Prop = EQ
  compare Prop (Type _) = LT
  compare (Type _) Prop = GT
  compare (Type m) (Type n) = compare m n
