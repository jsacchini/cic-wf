{-# LANGUAGE MultiParamTypeClasses, PackageImports, FlexibleInstances,
  UndecidableInstances
  #-}

{-| A common interface for monads which allow some kind of fresh name
    generation.

    Stolen from Agda. With minor changes
-}
module Utils.Fresh where

import "mtl" Control.Monad.State
import "mtl" Control.Monad.Reader

class BuildFresh i a where
    nextFresh :: a -> (i,a)

class (Monad m) => Fresh i m where
    fresh :: m i

instance (BuildFresh i s, MonadState s m) => Fresh i m where
    fresh = do (i,s) <- gets nextFresh
               put s
               return i

withFresh :: (BuildFresh i e, MonadReader e m) => (i -> m a) -> m a
withFresh ret = do (i,e) <- asks nextFresh
                   local (const e) $ ret i

