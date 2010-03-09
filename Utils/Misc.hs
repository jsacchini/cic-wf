module Utils.Misc where

import Control.Monad

appFst :: (a -> b) -> (a, c) -> (b, c)
appFst f (x,y) = (f x, y)

appSnd :: (a -> b) -> (c, a) -> (c, b)
appSnd f (x,y) = (x, f y)

appPair :: (a -> b) -> (a, a) -> (b, b)
appPair f (x,y) = (f x, f y)

mWhen :: (Monad m) => m Bool -> m () -> m ()
mWhen c n = do b <- c
               when b n
mUnless :: (Monad m) => m Bool -> m () -> m ()
mUnless c n = do b <- c
                 unless b n
