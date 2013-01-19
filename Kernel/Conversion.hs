{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances
  #-}

module Kernel.Conversion where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad
import Control.Monad.Reader

import qualified Data.Foldable as Fold

import Syntax.Common
import Syntax.Internal
import Kernel.Constraints
import Kernel.Whnf
import Kernel.TCM

import Utils.Misc
import Utils.Sized

class Conversion a where
  (~~) :: (MonadTCM tcm) => a -> a -> tcm Bool

conversion :: (MonadTCM tcm, Conversion a) => a -> a -> tcm Bool
conversion = (~~)

infixl 7 ~~

instance (Conversion a, Conversion b) => Conversion (a, b) where
  (x1, y1) ~~ (x2, y2) = x1 ~~ x2 `mAnd` y1 ~~ y2

instance Conversion a => Conversion (Maybe a) where
  Nothing ~~ Nothing = return True
  Just c1 ~~ Just c2 = c1 ~~ c2
  _ ~~ _ = return False

instance Conversion a => Conversion [a] where
  [] ~~ [] = return True
  (t1:ts1) ~~ (t2:ts2) = t1 ~~ t2 `mAnd` ts1 ~~ ts2
  _ ~~ _ = return False

instance Conversion Name where
  x1 ~~ x2 = return $ x1 == x2

instance Conversion Int where
  x1 ~~ x2 = return $ x1 == x2

instance Conversion Sort where
  (~~) s1 s2 = return (s1 == s2)

-- A more efficient version would only reduce to whnf
instance Conversion Term where
  (~~) t1 t2 =
    do n1 <- normalForm t1
       n2 <- normalForm t2
       case (n1, n2) of
         (Sort s1, Sort s2) -> s1 ~~ s2
         (Pi ctx1 t1, Pi ctx2 t2) ->
           ctx1 ~~ ctx2 `mAnd` pushCtx ctx1 (t1 ~~ t2)
         (Bound k1, Bound k2) -> k1 ~~ k2
         (Var x1, Var x2) -> x1 ~~ x2
         (Lam ctx1 t1, Lam ctx2 t2) ->
           ctx1 ~~ ctx2 `mAnd` pushCtx ctx1 (t1 ~~ t2)
         (App f1 ts1, App f2 ts2) -> f1 ~~ f2 `mAnd` ts1 ~~ ts2
         (Constr _ c1 _ ps1 as1, Constr _ c2 _ ps2 as2) ->
           c1 ~~ c2 `mAnd` ps1 ~~ ps2 `mAnd` as1 ~~ as2
         (Fix n1 f1 ctx1 tp1 body1, Fix n2 f2 ctx2 tp2 body2) ->
           f1 ~~ f2 `mAnd`
           n1 ~~ n2 `mAnd`
           eraseSize ctx1 ~~ eraseSize ctx2 `mAnd`
           eraseSize tp1 ~~ eraseSize tp2 `mAnd`
           pushBind (Bind f1 (mkPi ctx1 tp1)) (body1 ~~ body2)
         (Case c1, Case c2) -> c1 ~~ c2
         (Ind a1 x1, Ind a2 x2) -> do
           when (x1 == x2) $ addConstraints (a1 <<>> a2)
           when (x1 == x2) $ traceTCM_ ["adding constraints ", show a1, " <<>> ", show a2]
           x1 ~~ x2

         (_, _) -> return False

instance Conversion Bind where
  (~~) (Bind _ t1) (Bind _ t2) = (~~) t1 t2
  (~~) (LocalDef _ t1 t2) (LocalDef _ t3 t4) = t1 ~~ t3 `mAnd` t2 ~~ t4
  (~~) _ _ = return False

instance Conversion Context where
  (~~) EmptyCtx EmptyCtx = return True
  (~~) (ExtendCtx b1 c1) (ExtendCtx b2 c2) =
    b1 ~~ b2 `mAnd` pushBind b1 (c1 ~~ c2)

instance Conversion CaseTerm where
  (CaseTerm arg1 nmInd1 nmAs1 cin1 tp1 branches1) ~~ (CaseTerm arg2 nmInd2 nmAs2 cin2 tp2 branches2) =
    arg1 ~~ arg2 `mAnd` nmInd1 ~~ nmInd2 `mAnd`
    cin1 ~~ cin2 `mAnd` tp1 ~~ tp2 `mAnd` branches1 ~~ branches2

instance Conversion CaseIn where
  (CaseIn ctx1 nm1 args1) ~~ (CaseIn ctx2 nm2 args2) =
    ctx1 ~~ ctx2 `mAnd` nm1 ~~ nm2 `mAnd` args1 ~~ args2

instance Conversion Branch where
  (Branch nm1 _ _ body1 wh1) ~~ (Branch nm2 _ _ body2 wh2) =
    nm1 ~~ nm2 `mAnd` body1 ~~ body2 `mAnd` wh1 ~~ wh2

instance Conversion Subst where
  (Subst sg1) ~~ (Subst sg2) = sg1 ~~ sg2

class Conversion a => SubType a where
  (<~) :: (MonadTCM tcm) => a -> a -> tcm Bool


psubt :: (MonadTCM tcm, SubType a) => Polarity -> a -> a -> tcm Bool
psubt Pos  x y = x <~ y
psubt Neg  x y = y <~ x
psubt SPos x y = x <~ y
psubt Neut x y = x ~~ y

vsubt :: (MonadTCM tcm, SubType a) => [Polarity] -> [a] -> [a] -> tcm Bool
vsubt [] [] [] = return True
vsubt (p:ps) (x:xs) (y:ys) = psubt p x y `mAnd` vsubt ps xs ys
vsubt _ _ _ = __IMPOSSIBLE__


-- This instance expects that the arguments are actually types
instance SubType Term where
  t1 <~ t2 =
    do n1 <- normalForm t1
       n2 <- normalForm t2
       case (n1, n2) of
         (Pi ctx1 u1, Pi ctx2 u2) ->
           ctx2 <~  ctx1 `mAnd` pushCtx ctx2 (u1 <~ u2)
         -- TODO: check polarity of parameters
         (App (Ind a1 x1) ts1, App (Ind a2 x2) ts2)
           | x1 /= x2 -> return False
           | otherwise -> do
             Inductive ctxPars pols _ _ _ <- getGlobal x1
             let (pars1, args1) = splitAt (size ctxPars) ts1
             let (pars2, args2) = splitAt (size ctxPars) ts2
             -- traceTCM_ ["adding ", show a1, " <<= ", show a2]
             addConstraints (a1 <<= a2)
             vsubt pols pars1 pars2 `mAnd` args1 ~~ args2

         (Ind a1 x1, Ind a2 x2)
           | x1 /= x2 -> return False
           | otherwise -> do
             -- traceTCM_ ["adding ", show a1, " <<= ", show a2]
             addConstraints (a1 <<= a2)
             return True

         _ -> n1 ~~ n2

instance SubType Bind where
  (<~) (Bind _ t1) (Bind _ t2) = (<~) t1 t2
  (<~) (LocalDef _ t1 t2) (LocalDef _ t3 t4) = t1 ~~ t3 `mAnd` t2 <~ t4
  (<~) _ _ = return False

instance SubType Context  where
  (<~) EmptyCtx EmptyCtx = return True
  (<~) (ExtendCtx b1 c1) (ExtendCtx b2 c2) =
    b1 <~ b2 `mAnd` pushBind b1 (c1 <~ c2)
  (<~) _ _ = return False
