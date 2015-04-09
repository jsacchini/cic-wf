{-# LANGUAGE RankNTypes #-}

module CICwf.Utils.Lens where

import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Constant
import Data.Functor.Identity


-- | van Laarhoven lenses

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

mkLens :: (s -> a) -> (s -> a -> s) -> Lens' s a
mkLens getter setter f x = fmap (setter x) (f (getter x))

set :: Lens' s a -> (s -> a -> s)
set l x v = runIdentity $ l (const $ Identity v) x

(^.) :: s -> Lens' s a -> a
(^.) x l = getConstant $ l Constant x

over :: Lens' s a -> (a -> a) -> s -> s
over l f x = runIdentity $ l (Identity . f) x

-- | Set part of the state

use :: MonadState s m => Lens' s a -> m a
use l = gets (^. l)

(.=) :: MonadState s m => Lens' s a -> a -> m ()
l .= x = modify $ flip (set l) x

infix 4 .=


(%=) :: MonadState s m => Lens' s a -> (a -> a) -> m ()
l %= f = modify $ over l f

infix  4 %=

-- | Get part of the state

view :: MonadReader e m => Lens' e a -> m a
view l = asks (^. l)

locally :: MonadReader e m => Lens' e a -> (a -> a) -> m b -> m b
locally l = local . over l
