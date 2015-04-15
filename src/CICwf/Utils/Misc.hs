{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
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

{-# LANGUAGE PatternGuards #-}

-- | Miscellaneous functions.

module CICwf.Utils.Misc where

import Control.Monad

-- | @'appFst' f (x,y) = (f x, y)@
appFst :: (a -> b) -> (a, c) -> (b, c)
appFst f (x,y) = (f x, y)

-- | @'appSnd' f (x,y) = (x, f y)@
appSnd :: (a -> b) -> (c, a) -> (c, b)
appSnd f (x,y) = (x, f y)

-- | @'appPair' f (x,y) = (f x, f y)@
appPair :: (a -> b) -> (a, a) -> (b, b)
appPair f (x,y) = (f x, f y)

-- | Conjunction of booleans inside a monad.
mAnd :: (Monad m) => m Bool -> m Bool -> m Bool
infixl 5 `mAnd`
mAnd x y = do bx <- x
              by <- y
              return $ bx && by

-- | List version of 'mAnd'.
mAll :: (Monad m) => [m Bool] -> m Bool
infixl 5 `mAll`
mAll [] = return True
mAll (x:xs) = do b <- x
                 bs <- mAll xs
                 return (b && bs)


-- | Implication: @b1 '==>' b2 = not b1 || b2@
(==>) :: Bool -> Bool -> Bool
infixr 3 ==>
(==>) b1 b2 = not b1 || b2


-- | @'unlessM' b x@ executes @x@ if @b@ contains @False@.
unlessM :: (Monad m) => m Bool -> m () -> m ()
unlessM c n = do b <- c
                 unless b n

-- | @'whenM' b x@ executes @x@ if @b@ contains @True@.
whenM :: (Monad m) => m Bool -> m () -> m ()
whenM c n = do b <- c
               when b n

ifM :: (Monad m) => m Bool -> m a -> m a -> m a
ifM c t e = c >>= \b -> if b then t else e


-- | @'ifMaybe' x f y@ applies @f@ to @y@ if @x@ is @Just _@,
--   otherwise returns @y@.
ifMaybe :: Maybe a -> (b -> b) -> b -> b
ifMaybe (Just _) f x = f x
ifMaybe Nothing  _ x = x

findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
findMaybe _ [] = Nothing
findMaybe f (x : xs) | Just y <- f x = Just y
                     | otherwise     = findMaybe f xs

allMaybe :: (a -> Maybe b) -> [a] -> Maybe [b]
allMaybe _ [] = Just []
allMaybe f (x : xs) | Just y <- f x = allMaybe f xs >>= \ys -> return (y : ys)
                    | otherwise     = Nothing
