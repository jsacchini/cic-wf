{-
Copyright (c) 2005-2011 Ulf Norell, Nils Anders Danielsson, Catarina
Coquand, Makoto Takeyama, Andreas Abel, Karl Mehltretter, Marcin
Benke, Darin Morrison.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-| A common interface for monads which allow some kind of fresh name
    generation.

    Taken from Agda.
-}
module CICwf.Utils.Fresh where

import Control.Monad.Reader
import Control.Monad.State

class HasFresh i a where
    nextFresh :: a -> (i,a)

fresh :: (HasFresh i s, MonadState s m) => m i
fresh =
    do  (i,s) <- gets nextFresh
        put s
        return i

fresh' :: (HasFresh i s, MonadState s m) => (i -> a -> b) -> a -> m b
fresh' f x =
    do  (i,s) <- gets nextFresh
        put s
        return (f i x)

withFresh :: (HasFresh i e, MonadReader e m) => (i -> m a) -> m a
withFresh ret =
    do  (i,e) <- asks nextFresh
        local (const e) $ ret i
