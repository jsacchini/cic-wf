{-# LANGUAGE PackageImports, TypeSynonymInstances, DeriveDataTypeable,
  FlexibleInstances, CPP
 #-}

module Kernel.Conversion where

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import Control.Exception

import Data.Typeable

import Syntax.Bind
import Syntax.Internal
import Syntax.ETag
import Kernel.Whnf
import Kernel.TCM

class Conversion a where
    conversion :: (MonadTCM tcm) => a -> a -> tcm Bool

instance Conversion BindT where
    conversion b1 b2 = conversion (expr b1) (expr b2)

instance Conversion Term where
    conversion t1 t2 = do w1 <- whnf t1
                          w2 <- whnf t2
                          case (w1, w2) of
                            (Free x, Free y) -> return (x == y)
                            (Bound m, Bound n) -> return (m == n)
                            (TSort s1, TSort s2) -> return (s1 == s2)
                            (Pi u1 u2, Pi v1 v2) -> do b1 <- conversion u1 v1
                                                       b2 <- conversion u2 v2
                                                       return (b1 && b2)
                            (Lam u1 u2, Lam v1 v2) -> do b1 <- conversion u1 v1
                                                         b2 <- conversion u2 v2
                                                         return (b1 && b2)
                            (App u1 u2, App v1 v2) -> do b1 <- conversion u1 v1
                                                         b2 <- conversion u2 v2
                                                         return (b1 && b2)
                            (Constr _ x p1 a1, Constr _ y p2 a2) -> if x /= y then return False
                                                                    else do bps <- sequence (map (uncurry conversion) (zip p1 p2))
                                                                            bas <- sequence (map (uncurry conversion) (zip a1 a2))
                                                                            return $ and (bps ++ bas)
                            (_, _) -> return False
