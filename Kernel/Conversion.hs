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
import Syntax.Size
import Syntax.Internal
import Kernel.Constraints
import Kernel.Whnf
import Kernel.TCM

import Utils.Misc
import Utils.Sized


(<<=) :: Annot -> Annot -> [Constraint StageVar]
(<<=) (Size s1) (Size s2) =
  case (normalize s1, normalize s2) of
    (Just (a1, n1), Just (a2, n2)) -> [(a1, a2, n2 - n1)]
    (Nothing      , Just (a2, n2)) -> [(infty, a2, 0)]  -- ∞ ⊑ a2
    (_            , Nothing)       -> []  -- s ⊑ ∞
  where
    infty = inftyStageVar

(<<>>) :: Annot -> Annot -> [Constraint StageVar]
(<<>>) a1 a2 = a1 <<= a2 ++ a2 <<= a1


subSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Bool
subSort Prop     Prop     = return True -- Prop ⊈ Type(i)
subSort (Type m) (Type n) = do addTypeConstraints [(m, n, 0)] -- m <= n
                               return True
subSort _        _        = return False


subTypeSort :: (MonadTCM tcm) => Type -> Type -> tcm Bool
subTypeSort t1 t2 = do
  n1 <- nF t1
  n2 <- nF t2
  case (n1, n2) of
    (Sort s1, Sort s2) -> s1 `subSort` s2
    (Pi ctx1 t1, Pi ctx2 t2) ->
      ctx2 <~ ctx1 `mAnd` pushCtx ctx1 (t1 `subTypeSort` t2)
    (Ind a1 x1, Ind a2 x2)
      | x1 == x2  -> do addStageConstraints (a1 <<= a2)
                        return True
      | otherwise -> return False
    (App (Ind a1 x1) ts1, App (Ind a2 x2) ts2)
      | x1 == x2  -> do addStageConstraints (a1 <<= a2)
                        ts1 ~~ ts2
      | otherwise -> return False
    _ -> n1 ~~ n2


subType :: (MonadTCM tcm) => Term -> Term -> tcm Bool
subType t1 t2 = do
  n1 <- nF t1
  n2 <- nF t2
  n1 <~ n2


conv :: (MonadTCM tcm) => Term -> Term -> tcm Bool
conv t1 t2 = do
  n1 <- nF t1
  n2 <- nF t2
  n1 ~~ n2

class Conversion a where
  -- We assume that both arguments are in normal form
  -- TODO: A more efficient version would only assume whnf
  (<~) :: (MonadTCM tcm) => a -> a -> tcm Bool
  (~~) :: (MonadTCM tcm) => a -> a -> tcm Bool

infixl 7 ~~

-- instance (Conversion a, Conversion b) => Conversion (a, b) where
--   (x1, y1) <~ (x2, y2) = x1 <~ x2 `mAnd` y1 <~ y2

instance Conversion a => Conversion (Maybe a) where
  Nothing <~ Nothing = return True
  Just c1 <~ Just c2 = c1 <~ c2
  _ <~ _ = return False

  Nothing ~~ Nothing = return True
  Just c1 ~~ Just c2 = c1 ~~ c2
  _ ~~ _ = return False

instance Conversion a => Conversion [a] where
  [] <~ [] = return True
  (t1:ts1) <~ (t2:ts2) = t1 <~ t2 `mAnd` ts1 <~ ts2
  _ <~ _ = return False

  (~~) [] [] = return True
  (~~) (t1:ts1) (t2:ts2) = t1 ~~ t2 `mAnd` ts1 ~~ ts2
  (~~) _ _ = return False

instance Conversion Sort where
  (~~) Prop     Prop     = return True
  (~~) (Type m) (Type n) = do addTypeConstraints [(m, n, 0), (n, m, 0)] -- m = n
                              return True
  (~~) _        _        = return False

  (<~) = (~~)

instance Conversion Type where
  (~~) (Sort s1) (Sort s2) = s1 ~~ s2
  (~~) (Pi ctx1 t1) (Pi ctx2 t2) =
    ctx2 ~~ ctx1 `mAnd` pushCtx ctx1 (t1 ~~ t2)
  (~~) (Ind a1 x1) (Ind a2 x2)
     | x1 == x2 = do addStageConstraints (a1 <<>> a2)
                     return True
     | otherwise = return False
  (~~) (App (Ind a1 x1) ts1) (App (Ind a2 x2) ts2)
     | x1 == x2  = do addStageConstraints (a1 <<>> a2)
                      ts1 ~~ ts2
     | otherwise = return False
  (~~) (Bound k1) (Bound k2) = return $ k1 == k2
  (~~) (Var x1) (Var x2) = return $ x1 == x2
  (~~) (Lam ctx1 t1) (Lam ctx2 t2) =
    ctx1 ~~ ctx2 `mAnd` pushCtx ctx1 (t1 ~~ t2)
  (~~) (App f1 ts1) (App f2 ts2) = f1 ~~ f2 `mAnd` ts1 ~~ ts2
  (~~) (Constr c1 _ ps1 as1) (Constr c2 _ ps2 as2) =
    return (c1 == c2) `mAnd` ps1 ~~ ps2 `mAnd` as1 ~~ as2
  (~~) (Fix f1) (Fix f2) = f1 ~~ f2
  (~~) (Case c1) (Case c2) = c1 ~~ c2
  (~~) _ _ = return False


  (<~) (Sort s1) (Sort s2) = s1 <~ s2
  (<~) (Pi ctx1 t1) (Pi ctx2 t2) =
    ctx2 <~ ctx1 `mAnd` pushCtx ctx1 (t1 <~ t2)
  (<~) (Ind a1 x1) (Ind a2 x2)
     | x1 == x2 = do addStageConstraints (a1 <<= a2)
                     return True
     | otherwise = return False
  (<~) (App (Ind a1 x1) ts1) (App (Ind a2 x2) ts2)
     | x1 == x2  = do ind <- getGlobal x1
                      case ind of
                        Inductive {} -> do addStageConstraints (a1 <<= a2)
                                           let pol = indPol ind
                                               numPars = length pol
                                               (par1, arg1) = splitAt numPars ts1
                                               (par2, arg2) = splitAt numPars ts2
                                           vsubt pol par1 par2 `mAnd` arg1 ~~ arg2
                        _ -> __IMPOSSIBLE__ -- sanity check
     | otherwise = return False
  (<~) t1 t2 = t1 ~~ t2


instance Conversion FixTerm where
  (~~) (FixTerm k1 n1 f1 ctx1 tp1 body1) (FixTerm k2 n2 f2 ctx2 tp2 body2) =
    return (k1 == k2) `mAnd`
    return (f1 == f2) `mAnd`
    return (n1 == n2) `mAnd`
    eraseSize ctx1 ~~ eraseSize ctx2 `mAnd`
    eraseSize tp1 ~~ eraseSize tp2 `mAnd`
    pushBind (mkBind f1 (mkPi ctx1 tp1)) (body1 ~~ body2)

  (<~) = (~~)

instance Conversion Bind where
  (<~) b1 b2 = bindType b1 <~ bindType b2 `mAnd` bindDef b1 ~~ bindDef b2

  (~~) b1 b2 = bindType b1 ~~ bindType b2 `mAnd` bindDef b1 ~~ bindDef b2

instance Conversion Context where
  (<~) CtxEmpty CtxEmpty = return True
  (<~) (CtxExtend b1 c1) (CtxExtend b2 c2) =
    b1 <~ b2 `mAnd` pushBind b1 (c1 <~ c2)

  (~~) CtxEmpty CtxEmpty = return True
  (~~) (CtxExtend b1 c1) (CtxExtend b2 c2) =
    b1 ~~ b2 `mAnd` pushBind b1 (c1 ~~ c2)


instance Conversion CaseTerm where
  (CaseTerm arg1 nmInd1 nmAs1 cin1 tp1 branches1) ~~ (CaseTerm arg2 nmInd2 nmAs2 cin2 tp2 branches2) =
    arg1 ~~ arg2 `mAnd` return (nmInd1 == nmInd2) `mAnd`
    inRet cin1 cin2 `mAnd` tp1 ~~ tp2 `mAnd` branches1 ~~ branches2
    where
      inRet (Just c1) (Just c2) = c1 ~~ c2
      inRet Nothing Nothing = return True
      inRet _ _ = return False

  (<~) = (~~)

instance Conversion CaseIn where
  (CaseIn ctx1 nm1 args1) ~~ (CaseIn ctx2 nm2 args2) =
    ctx1 ~~ ctx2 `mAnd` return (nm1 == nm2) `mAnd` args1 ~~ args2

  (<~) = (~~)

instance Conversion Branch where
  (Branch nm1 _ _ body1 wh1) ~~ (Branch nm2 _ _ body2 wh2) =
    return (nm1 == nm2) `mAnd` body1 ~~ body2 `mAnd` wh1 ~~ wh2

  (<~) = (~~)

instance Conversion Subst where
  (Subst sg1) ~~ (Subst sg2) = conv sg1 sg2
    where
      conv :: (MonadTCM tcm) => [(Int,Term)] -> [(Int,Term)] -> tcm Bool
      conv [] [] = return True
      conv ((n1,t1):sg1) ((n2,t2):sg2) =
        return (n1 == n2) `mAnd` t1 ~~ t2 `mAnd` conv sg1 sg2
      conv _ _ = return False

  (<~) = (~~)

psubt :: (MonadTCM tcm, Conversion a) => Polarity -> a -> a -> tcm Bool
psubt Pos  x y = x <~ y
psubt Neg  x y = y <~ x
psubt SPos x y = x <~ y
psubt Neut x y = x ~~ y

vsubt :: (MonadTCM tcm, Conversion a) => [Polarity] -> [a] -> [a] -> tcm Bool
vsubt [] [] [] = return True
vsubt (p:ps) (x:xs) (y:ys) = psubt p x y `mAnd` vsubt ps xs ys
vsubt _ _ _ = __IMPOSSIBLE__
