module Utils.Misc where

import Text.ParserCombinators.Parsec

appFst :: (a -> b) -> (a, c) -> (b, c)
appFst f (x,y) = (f x, y)

appSnd :: (a -> b) -> (c, a) -> (c, b)
appSnd f (x,y) = (x, f y)
