{-# LANGUAGE PackageImports, TypeSynonymInstances, CPP #-}

module Kernel.Conversion where

import "mtl" Control.Monad.State
import Syntax.Internal
import Syntax.ETag
import Kernel.Whnf
import Kernel.TCM


class Conversion a where
    conversion :: (MonadTCM tcm) => a -> a -> tcm ()

instance Conversion Bind where
    conversion b1 b2 = conversion (expr b1) (expr b2)

instance Conversion Term where
    conversion t1 t2 = do w1 <- whnf t1
                          w2 <- whnf t2
                          case (w1, w2) of
                            (Free x, Free y) -> when (x /= y) (typeError $ NotConvertible t1 t2)
                            (Bound m, Bound n) -> when (m /= n) (typeError $ NotConvertible t1 t2)
                            (TSort s1, TSort s2) -> when (s1 /= s2) (typeError $ NotConvertible t1 t2)
                            (Pi u1 u2, Pi v1 v2) -> conversion u1 v1 >> conversion u2 v2
                            (Lam u1 u2, Lam v1 v2) -> conversion u1 v1 >> conversion u2 v2
                            (App u1 u2, App v1 v2) -> conversion u1 v1 >> conversion u2 v2
                            (_, _) -> typeError $ NotConvertible t1 t2
