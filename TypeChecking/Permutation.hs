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

{-# LANGUAGE FlexibleInstances, CPP #-}

module TypeChecking.Permutation where

import qualified Data.Foldable as Fold

#include "../undefined.h"
import Utils.Impossible

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Common
import Utils.Misc

-- | Permutation of bound variables.
--
--   Invariant (Perm xs) :  sort xs == [0..length xs - 1]
--
--   Perm [x0 ... xn] :: [a0 ... an] -> [a_x1 ... a_xn]
data Permutation = Perm { unPerm :: [Int] }
                   deriving(Show)

idP :: Int -> Permutation
idP k = Perm [0..k-1]

combineP :: Permutation -> Permutation -> Permutation
combineP (Perm p1) (Perm p2)
  | null p1 && null p2 = Perm []
  | length p1 == length p2 = Perm $ map (uncurry (!!)) (zip (repeat p1) p2)
  | otherwise = __IMPOSSIBLE__

(++>) :: Permutation -> Int -> Permutation
(++>) (Perm xs) k = Perm $ xs ++ [len..len+k-1]
  where len = length xs

(<++) :: Int -> Permutation -> Permutation
(<++) k (Perm xs) = Perm $ [0..k-1] ++ map (+k) xs


insertP :: Int -> Permutation -> Permutation
insertP k (Perm xs) = Perm $ (map liftF xs) ++ [k]
  where liftF x | x >= k = x + 1
                | otherwise = x


-- | Applying a permutation

class ApplyPerm a where
  applyPerm :: Permutation -> a -> a

instance ApplyPerm Int where
  applyPerm (Perm xs) k | k < length xs = xs !! k
                        | otherwise     = k

instance (ApplyPerm a) => ApplyPerm (Maybe a) where
  applyPerm = fmap . applyPerm

instance (ApplyPerm a) => ApplyPerm (Implicit a) where
  applyPerm = fmap . applyPerm

instance ApplyPerm a => ApplyPerm (a, a) where
  applyPerm p (t1, t2) = (applyPerm p t1, applyPerm p t2)

instance ApplyPerm a => ApplyPerm [a] where
  applyPerm = map . applyPerm

instance (ApplyPerm a, HasNames a) => ApplyPerm (Ctx a) where
  applyPerm p CtxEmpty = CtxEmpty
  applyPerm p (CtxExtend x xs) =
    CtxExtend (applyPerm p x) (applyPerm (length (name x) <++ p) xs)


------------------------------------------------------------
-- instance of ApplyPerm to Intenal syntax
------------------------------------------------------------

instance ApplyPerm Bind where
  applyPerm p b = b { bindType = applyPerm p (bindType b)
                    , bindDef  = applyPerm p (bindDef b) }


instance ApplyPerm Term where
  applyPerm _ t@(Sort _) = t
  applyPerm p (Pi c t) = Pi (applyPerm p c) (applyPerm (ctxLen c <++ p) t)
  applyPerm p t@(Bound k) | k < length (unPerm p) = Bound $ (unPerm p) !! k
                          | otherwise = t
  applyPerm p t@(Var _) = t
  applyPerm p (Lam c t) = Lam (applyPerm p c) (applyPerm (ctxLen c <++ p) t)
  applyPerm p (App t1 t2) = App (applyPerm p t1) $ map (applyPerm p) t2
  applyPerm p t@(Ind _ _) = t
  applyPerm p (Constr x indId ps as) = Constr x indId ps' as'
    where ps' = map (applyPerm p) ps
          as' = map (applyPerm p) as
  applyPerm p (Fix f) = Fix (applyPerm p f)
  applyPerm p (Case c) = Case (applyPerm p c)

instance ApplyPerm FixTerm where
  applyPerm p (FixTerm a n x bs t e) =
    FixTerm a n x (applyPerm p bs) (applyPerm (ctxLen bs <++ p) t)
    (applyPerm (ctxLen bs <++ p) e)

instance ApplyPerm CaseTerm where
  applyPerm p (CaseTerm arg nm cas cin ret branches) =
    CaseTerm (applyPerm p arg) nm cas (applyPerm p cin) (applyPerm p ret) (map (applyPerm p) branches)

instance ApplyPerm CaseIn where
  applyPerm p (CaseIn binds nmInd args) =
    CaseIn (applyPerm p binds) nmInd
    (map (applyPerm (ctxLen binds <++ p)) args)

instance ApplyPerm Branch where
  applyPerm p (Branch nm cid nmArgs body whSubst) =
    Branch nm cid nmArgs (applyPerm (length nmArgs <++ p) body)
    (applyPerm (length nmArgs <++ p) whSubst)

instance ApplyPerm Subst where
  applyPerm p (Subst sg) = Subst $ map (appSnd (applyPerm p)) sg



------------------------------------------------------------
-- instance of ApplyPerm to Abstract syntax
------------------------------------------------------------

instance ApplyPerm A.Expr where
  applyPerm p (A.Ann r e1 e2) = A.Ann r (applyPerm p e1) (applyPerm p e2)
  applyPerm _ t@(A.Sort _ _) = t
  applyPerm p (A.Pi r bs e) =
    A.Pi r (applyPerm p bs) (applyPerm (length (name bs) <++ p) e)
  applyPerm p (A.Arrow r e1 e2) =
    A.Arrow r (applyPerm p e1) (applyPerm (1 <++ p) e2)
  applyPerm p t@(A.Bound r x k)
    | k < length (unPerm p) = A.Bound r x $ (unPerm p) !! k
    | otherwise = t
  applyPerm _ t@(A.Ident _ _) = t
  applyPerm p (A.Lam r bs e) =
    A.Lam r (applyPerm p bs) (applyPerm (length (name bs) <++ p) e)
  applyPerm p (A.App r e1 e2) = A.App r (applyPerm p e1) (applyPerm p e2)
  applyPerm p t@(A.Ind _ _ _ _) = t
  applyPerm p (A.Constr r x indId ps as) = A.Constr r x indId ps' as'
    where ps' = map (applyPerm p) ps
          as' = map (applyPerm p) as
  applyPerm p (A.Fix f) = A.Fix $ applyPerm p f
  applyPerm p (A.Case c) = A.Case $ applyPerm p c
  applyPerm p (A.Number _ _) = __IMPOSSIBLE__

instance ApplyPerm A.Bind where
  applyPerm p (A.Bind r xs e) = A.Bind r xs (applyPerm p e)

-- permBinds :: Permutation -> [A.Bind] -> [A.Bind]
-- permBinds p [] = []
-- permBinds p (A.Bind r xs e:bs) =
--   A.Bind r xs (applyPerm p e) : permBinds (length xs <++ p) bs

instance ApplyPerm A.CaseExpr where
  applyPerm p (A.CaseExpr r arg cas cin whSubst ret branches) =
    A.CaseExpr r (applyPerm p arg) cas (applyPerm p cin)
    (applyPerm p whSubst)
    (applyPerm (len <++ p) ret) (map (applyPerm (lencin <++ p)) branches)
      where len = length (name cas) + lencin
            lencin = length (name cin)

instance ApplyPerm A.FixExpr where
  applyPerm p (A.FixExpr a r k nm tp body) =
    A.FixExpr a r k nm (applyPerm p tp) (applyPerm (1 <++ p) body)

instance ApplyPerm A.Subst where
  applyPerm p (A.Subst sg) = A.Subst (map (applyPerm p) sg)

instance ApplyPerm A.Assign where
  applyPerm p (A.Assign r n x e) = A.Assign r n x (applyPerm p e)

instance ApplyPerm A.CaseIn where
  applyPerm p (A.CaseIn r binds nmInd args) =
    A.CaseIn r (applyPerm p binds) nmInd
    (map (applyPerm (length (name binds) <++ p)) args)

instance ApplyPerm A.Branch where
  applyPerm p (A.Branch r nm cid nmArgs body whSubst) =
    A.Branch r nm cid nmArgs (applyPerm (length nmArgs <++ p) body)
    (applyPerm (length nmArgs <++ p) whSubst)
