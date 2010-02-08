{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, MultiParamTypeClasses,
  FlexibleContexts, FunctionalDependencies, UndecidableInstances
 #-}
{-# LANGUAGE CPP #-}

-- Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Data.Function

import Syntax.Position
import qualified Syntax.Abstract as A
import Syntax.ETag

data Sort 
    = Box
    | Star
    deriving(Eq, Show)

type Name = String

type MetaId = Int
type Shift = Int
type CxtSize = Int

data Term a where
    TSort :: (ETag a) => Sort -> Term a
    Pi :: (ETag a) => Name -> Term a -> Term a -> Term a
    Bound :: (ETag a) => Int -> Term a
    Free :: (ETag a) => Name -> Term a
    Lam :: (ETag a) => Name -> Term a -> Term a -> Term a
    App :: (ETag a) => Term a -> Term a -> Term a
    Meta :: MetaId -> Shift -> CxtSize -> Term EVAR

type Type a = Term a

data Global a
    = Def (Type a) (Term a)
--    | Ind NamedCxt NamedCxt Sort [ConstrType]
    | Axiom (Type a)
    deriving(Show)

type NamedCxt a = [(Name, Term a)]

instance Show (Term a) where
    show = show . reify

lift :: Int -> Int -> Term a -> Term a
lift k n t@(TSort _) = t
lift k n (Pi x t1 t2) = Pi x (lift k n t1) (lift k (n+1) t2)
lift k n t@(Bound m) = if m < n then t else Bound $ m+k
lift k n t@(Free _) = t
lift k n (Lam x t u) = Lam x (lift k n t) (lift k (n+1) u)
lift k n (App t1 t2) = App (lift k n t1) (lift k n t2)
lift k n t@(Meta i m s) = if m < n then t else Meta i (m+k) s

subst_ :: Int -> Term a -> Term a -> Term a
subst_ i r t@(TSort _) = t
subst_ i r (Pi x t1 t2) = Pi x (subst_ i r t1) (subst_ (i+1) r t2)
subst_ i r t@(Bound n) | n < i = t
                       | n == i = lift i 0 r
		       | otherwise = Bound (n-1)
subst_ i r t@(Free _) = t
subst_ i r (Lam x t u) = Lam x (subst_ i r t) (subst_ (i+1) r u)
subst_ i r (App t1 t2) = App (subst_ i r t1) (subst_ i r t2)
subst_ i r t@(Meta _ _ _) = t

subst :: Term a -> Term a -> Term a
subst = subst_ 0

multisubst :: Int -> [Term a] -> Term a -> Term a
multisubst i ts u = snd $ foldl (\(i, t) r -> (i+1, subst_ i r t)) (i, u) ts

mapsubst :: Int -> Term a -> [Term a] -> [Term a]
mapsubst n t [] = []
mapsubst n t (u:us) = subst_ n t u : mapsubst (n+1) t us

isFree :: Int -> Term a -> Bool
isFree _ (TSort _) = False
isFree n (Pi _ t1 t2) = isFree n t1 || isFree (n+1) t2
isFree n (Bound m) = n == m
isFree _ (Free _) = False
isFree n (Lam _ t u) = isFree n t || isFree (n+1) u
isFree n (App t1 t2) = isFree n t1 || isFree n t2

substMeta :: MetaId -> Term a -> Term a -> Term a
substMeta i r t@(TSort _) = t
substMeta i r (Pi x t1 t2) = Pi x (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Bound _) = t
substMeta i r t@(Free _) = t
substMeta i r (Lam x t u) = Lam x (substMeta i r t) (substMeta i r u)
substMeta i r (App t1 t2) = App (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Meta j _ _) | i == j = r
                             | otherwise = t


class Interp a where
    interp :: a -> Term NM

instance Interp A.Sort where
    interp A.Box = TSort Box
    interp A.Star = TSort Star

instance Interp A.Expr where
    interp (A.Ann _ t u) = interp t
    interp (A.TSort _ s) = interp s
    interp (A.Pi _ x t1 t2) = Pi x (interp t1) (interp t2)
    interp (A.Bound _ n) = Bound n
    interp (A.Free _ x) = Free x
    interp (A.Lam _ x t u) = Lam x (interp t) (interp u)
    interp (A.App _ t1 t2) = App (interp t1) (interp t2)

-- class Reify a where
--     reify :: a -> A.Expr b

-- instance Reify Sort where
--     reify Box = A.TSort noPos A.Box
--     reify Star = A.TSort noPos A.Star


-- instance Reify (Term a) where 
reify t = reify_ (collectFree t) t

freshName :: [Name] -> Name -> Name
freshName xs y | notElem y xs = y
               | otherwise = addSuffix 0
                             where addSuffix n | notElem (y++show n) xs = y++show n
                                               | otherwise = addSuffix (n+1)

collectFree :: Term a -> [Name]
collectFree (TSort _) = []
collectFree (Pi _ t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Bound _) = []
collectFree (Free x) = [x]
collectFree (Lam _ t1 t2) = collectFree t1 ++ collectFree t2
collectFree (App t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Meta _ _ _) = []

reify_ :: [Name] -> Term a -> A.Expr
reify_ xs (TSort Box) = A.TSort noPos A.Box
reify_ xs (TSort Star) = A.TSort noPos A.Star
reify_ xs (Pi x t1 t2) = A.Pi noPos x' (reify_ xs t1) (reify_ (x:xs) t2)
                         where x' = freshName xs x
reify_ xs (Bound n) = A.Bound noPos n
reify_ xs (Free x) = A.Free noPos x
reify_ xs (Lam x t u) = A.Lam noPos x' (reify_ xs t) (reify_ (x:xs) u)
                        where x' = freshName xs x
reify_ xs (App t1 t2) = A.App noPos (reify_ xs t1) (reify_ xs t2)
reify_ xs (Meta i _ _) = A.EVar noPos (Just i)



class (ETag a, ETag b) => CastExpr a b | a -> b where
    cast :: Term a -> Term b

instance (ETag a) => CastExpr NM a where
    cast (TSort s) = TSort s
    cast (Pi x t1 t2) = Pi x (cast t1) (cast t2)
    cast (Bound n) = Bound n
    cast (Free x) = Free x
    cast (Lam x t1 t2) = Lam x (cast t1) (cast t2)
    cast (App t1 t2) = App (cast t1) (cast t2)

instance CastExpr EVAR NM where
    cast (TSort s) = TSort s
    cast (Pi x t1 t2) = Pi x (cast t1) (cast t2)
    cast (Bound n) = Bound n
    cast (Free x) = Free x
    cast (Lam x t1 t2) = Lam x (cast t1) (cast t2)
    cast (App t1 t2) = App (cast t1) (cast t2)
    cast (Meta _ _ _) = __IMPOSSIBLE__

-- instance CastExpr EVAR where
-- --cast :: (ETag a) => Term NM -> Term a
--     cast (TSort s) = TSort s
--     cast (Pi x t1 t2) = Pi x (cast t1) (cast t2)
--     cast (Bound n) = Bound n
--     cast (Free x) = Free x
--     cast (Lam x t1 t2) = Lam x (cast t1) (cast t2)
--     cast (App t1 t2) = App (cast t1) (cast t2)
--     cast (Meta i n s) = Meta i n s
-- instance CastExpr EVAR NM where
--     cast (TSort s) = TSort s
--     cast (Pi x t1 t2) = Pi x (cast t1) (cast t2)
--     cast (Bound n) = Bound n
--     cast (Free x) = Free x
--     cast (Lam x t1 t2) = Lam x (cast t1) (cast t2)
--     cast (App t1 t2) = App (cast t1) (cast t2)


