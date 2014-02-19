{- Simple Maybe monad transformer -}

module CICminus.Utils.Maybe where

import Control.Monad.Trans

data MaybeT m a = MaybeT { runMT :: m (Maybe a) }

instance (Monad m) => Monad (MaybeT m) where
  m >>= f = MaybeT $ do a <- runMT m
                        case a of
                            Just x -> runMT (f x)
                            Nothing -> return Nothing
  return a = MaybeT $ return (Just a)
  fail _ = MaybeT $ return Nothing

instance MonadTrans MaybeT where
  lift m = MaybeT $ do
                     a <- m
                     return (Just a)
