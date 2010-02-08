{-# LANGUAGE PackageImports, CPP #-}

module Kernel.Conversion where

import "mtl" Control.Monad.State
import Syntax.Internal
import Syntax.ETag
import Kernel.Whnf
import Kernel.TCM

conversion :: (MonadTCM tcm) => Term NM -> Term NM -> tcm ()
conversion t1 t2 = do w1 <- whnf t1
                      w2 <- whnf t2
                      case (w1, w2) of
                        (Free x, Free y) -> when (x /= y) (typeError $ NotConvertible t1 t2)
                        (Bound m, Bound n) -> when (m /= n) (typeError $ NotConvertible t1 t2)
                        (TSort s1, TSort s2) -> when (s1 /= s2) (typeError $ NotConvertible t1 t2)
                        (Pi _ u1 u2, Pi _ v1 v2) -> conversion u1 v1 >> conversion u2 v2
                        (Lam _ u1 u2, Lam _ v1 v2) -> conversion u1 v1 >> conversion u2 v2
                        (App u1 u2, App v1 v2) -> conversion u1 v1 >> conversion u2 v2
                        (_, _) -> typeError $ NotConvertible t1 t2
