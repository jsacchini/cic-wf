-- | Sizes

module Syntax.Size where

import Text.PrettyPrint

import Data.Function
import Data.Functor

import Utils.Pretty
import Utils.Misc

data Size =
  Svar Int
  | Hat Size
  | Infty

base :: Size -> Maybe Int
base (Svar n) = Just n
base (Hat s) = base s
base Infty    = Nothing

numHat :: Size -> Int
numHat (Svar _) = 0
numHat (Hat s) = numHat s + 1
numHat Infty    = 0

normalize :: Size -> Maybe (Int, Int)
normalize (Svar n) = Just (n, 0)
normalize (Hat s) = appSnd (+1) <$> normalize s
normalize Infty    = Nothing

-- | The relation between 'normalize', 'base' and 'numHat' is the following:
--
--   base s = Just n    ==>  normalize s = Just (n, numHat s)
--     s is a variable with many hats on top
--   base s = Nothing   ==>  normalize s = Nothing
--     s is Infty with many hats on top

instance Eq Size where
  (==) = (==) `on` normalize

instance Pretty Size where
  prettyPrint s =
    case normalize s of
      Just (v, n) -> text $ "a" ++ show v ++ show "^" ++ show n
      Nothing     -> text "oo"

instance Show Size where
  show = show . prettyPrint