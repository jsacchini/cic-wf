module Utils.Sized where

class Sized a where
  size :: (Num t) => a -> t

instance Sized a => Sized (Maybe a) where
  size = maybe 0 size
