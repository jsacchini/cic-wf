{-# LANGUAGE TypeSynonymInstances, FlexibleInstances
  #-}

module Kernel.Conversion where

import Control.Monad
import Control.Monad.Reader

import Syntax.Common
import Syntax.Internal
import Kernel.Constraints
import Kernel.Whnf
import Kernel.TCM
import Utils.Misc

class Conversion a where
  conversion :: (MonadTCM tcm) => a -> a -> tcm Bool

-- instance Conversion a => Conversion [a] where
--   conversion [] [] = return True
--   conversion (x:xs) (y:ys) = conversion x y `mAnd` conversion xs ys
--   conversion _ _ = return False


instance Conversion Bind where
  conversion (Bind _ t1) (Bind _ t2) = conversion t1 t2
  conversion (LocalDef _ t1 t2) (LocalDef _ t3 t4) = conversion t1 t3 `mAnd` conversion t2 t4
  conversion _ _ = return False

instance Conversion Context where
  conversion EmptyCtx EmptyCtx = return True
  conversion (ExtendCtx b1 c1) (ExtendCtx b2 c2) =
    do x1 <- conversion b1 b2
       x2 <- conversion c1 c2
       return $ x1 && x2

instance Conversion Sort where
  conversion s1 s2 = return (s1 == s2)

-- A more efficient version would only reduce to whnf
instance Conversion Term where
  conversion t1 t2 =
    do n1 <- normalForm t1
       n2 <- normalForm t2
       return (n1 == n2)


class SubType a where
  subtype :: (MonadTCM tcm) => a -> a -> tcm Bool


-- This instance expects that the arguments are actually types
instance SubType Type where
  subtype t1 t2 =
    do n1 <- whnf t1
       n2 <- whnf t2
       case (n1, n2) of
         (Pi bs1 u1, Pi bs2 u2) ->
           subtype bs2 bs1 `mAnd` subtype u1 u2
         (App (Ind a1 x1) ts1, App (Ind a2 x2) ts2) ->
           addConstraints (a1 <<= a2) >> return True

instance SubType Context where
  subtype _ _ = return False
