{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

-- | Misc functions.

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

mAll :: (Monad m) => [m Bool] -> m Bool
mAll [] = return True
mAll (x:xs) = do b <- x
                 bs <- mAll xs
                 return (b && bs)

infixl 5 `mAnd`
infixl 5 `mAll`

(==>) :: Bool -> Bool -> Bool
(==>) b1 b2 = not b1 || b2

infixr 3 ==>

-- This two functions could be eliminated
whenM :: (Monad m) => m Bool -> m () -> m ()
whenM c n = do b <- c
               when b n
unlessM :: (Monad m) => m Bool -> m () -> m ()
unlessM c n = do b <- c
                 unless b n

foldInt :: (Int -> a -> b -> b) -> Int -> [a] -> b -> b
foldInt _ _ [] x = x
foldInt f n (t:ts) x = foldInt f n ts (f n t x)

foldrAcc :: (b -> a -> c -> c) -> (b -> a -> b) -> b -> c -> [a] -> c
foldrAcc _ _ _   r [] = r
foldrAcc f g acc r (x:xs) = f acc x (foldrAcc f g (g acc x) r xs)

-- Replaced by [n..]
-- from :: Int -> [Int]
-- from n = n : from (n + 1)

ifMaybe :: Maybe a -> (a -> b -> c) -> (b -> c) -> b -> c
ifMaybe (Just c) f g x = f c x
ifMaybe Nothing f g x = g x

ifMaybe_ :: Maybe a -> (b -> b) -> b -> b
ifMaybe_ (Just c) f x = f x
ifMaybe_ Nothing  f x = x
