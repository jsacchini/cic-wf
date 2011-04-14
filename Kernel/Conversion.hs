{-# LANGUAGE PackageImports, TypeSynonymInstances, DeriveDataTypeable,
  FlexibleInstances, CPP
 #-}

module Kernel.Conversion where

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import Control.Exception

import Data.Typeable

import Syntax.Internal
import Kernel.Whnf
import Kernel.TCM
import Utils.Misc

class Conversion a where
  conversion :: (MonadTCM tcm) => a -> a -> tcm Bool

instance Conversion a => Conversion [a] where
  conversion [] [] = return True
  conversion (x:xs) (y:ys) = conversion x y `mAnd` conversion xs ys
  conversion _ _ = return False


instance Conversion Bind where
  conversion (Bind _ t1) (Bind _ t2) = conversion t1 t2
  conversion (LocalDef _ t1 t2) (LocalDef _ t3 t4) = conversion t1 t3 `mAnd` conversion t2 t4
  conversion _ _ = return False

instance Conversion Term where
    conversion t1 t2 =
      do w1 <- whnf t1
         w2 <- whnf t2
         case (w1, w2) of
           (Var x, Var y) -> return (x == y)
           (Bound _ m, Bound _ n) -> return (m == n)
           (Sort s1, Sort s2) -> return (s1 == s2)
           (Pi u1 u2, Pi v1 v2) -> do b1 <- conversion u1 v1
                                      b2 <- conversion u2 v2
                                      return (b1 && b2)
           (Lam u1 u2, Lam v1 v2) -> do b1 <- conversion u1 v1
                                        b2 <- conversion u2 v2
                                        return (b1 && b2)
           (App u1 u2, App v1 v2) -> do b1 <- conversion u1 v1
                                        b2 <- conversion u2 v2
                                        return (b1 && b2)
           -- (Constr _ x p1 a1, Constr _ y p2 a2) -> if x /= y then return False
           --                                         else do bps <- sequence (map (uncurry conversion) (zip p1 p2))
           --                                                 bas <- sequence (map (uncurry conversion) (zip a1 a2))
           --                                                 return $ and (bps ++ bas)
           (_, _) -> return False


(===) :: (MonadTCM) tcm => Term -> Term -> tcm ()
(===) x y = do b <- conversion x y
               if b
                 then return ()
                 else ask >>= \e -> typeError $ NotConvertible e x y
