module Utils.Misc where

import Control.Monad

appFst :: (a -> b) -> (a, c) -> (b, c)
appFst f (x,y) = (f x, y)

appSnd :: (a -> b) -> (c, a) -> (c, b)
appSnd f (x,y) = (x, f y)

appPair :: (a -> b) -> (a, a) -> (b, b)
appPair f (x,y) = (f x, f y)

mAnd :: (Monad m) => m Bool -> m Bool -> m Bool
mAnd x y = do bx <- x
              by <- y
              return $ bx && by

mWhen :: (Monad m) => m Bool -> m () -> m ()
mWhen c n = do b <- c
               when b n
mUnless :: (Monad m) => m Bool -> m () -> m ()
mUnless c n = do b <- c
                 unless b n

foldInt :: (Int -> a -> b -> b) -> Int -> [a] -> b -> b
foldInt _ _ [] x = x
foldInt f n (t:ts) x = foldInt f n ts (f n t x)

foldrAcc :: (b -> a -> c -> c) -> (b -> a -> b) -> b -> c -> [a] -> c
foldrAcc f g acc r [] = r
foldrAcc f g acc r (x:xs) = f acc x (foldrAcc f g (g acc x) r xs)

-- Replaced by [n..]
-- from :: Int -> [Int]
-- from n = n : from (n + 1)
