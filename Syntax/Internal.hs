{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, MultiParamTypeClasses,
  FlexibleContexts, FunctionalDependencies, UndecidableInstances
 #-}
{-# LANGUAGE CPP #-}

-- Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Data.Function
import Data.Foldable hiding (notElem)
import Data.Monoid

import Syntax.Position
import qualified Syntax.Abstract as A
import Syntax.ETag

data Sort 
    = Box
    | Star
    deriving(Eq, Show)

box :: (ETag a) => GTerm a
box = TSort Box
star :: (ETag a) => GTerm a
star = TSort Star

type Name = String

type MetaId = Int
type Shift = Int
type CxtSize = Int

data GTerm a where
    TSort :: (ETag a) => Sort -> GTerm a
    Pi :: (ETag a) => GBind (GType a) -> GTerm a -> GTerm a
    Bound :: (ETag a) => Int -> GTerm a
    Free :: (ETag a) => Name -> GTerm a
    Lam :: (ETag a) => GBind (GType a) -> GTerm a -> GTerm a
    App :: (ETag a) => GTerm a -> GTerm a -> GTerm a
    Meta :: MetaId -> Shift -> CxtSize -> GTerm EVAR

type GType a = GTerm a
--               deriving(Show)

type GNamedCxt a = [GBind a]

data GBind a = Bind Name a
             | NoBind a
             deriving(Show) -- we never call directly show for binds

instance Functor GBind where
    fmap f (NoBind t) = NoBind $ f t
    fmap f (Bind x t) = Bind x $ f t

instance Foldable GBind where
    foldMap f (NoBind t) = f t
    foldMap f (Bind _ t) = f t

expr :: GBind a -> a
expr (NoBind t) = t
expr (Bind _ t) = t

bind :: GBind a -> Name
bind (NoBind _) = ""
bind (Bind x _) = x

type Term = GTerm NM
type Type = GTerm NM
type ETerm = GTerm EVAR
type EType = GTerm EVAR
type NamedCxt = GNamedCxt Term
type ENamedCxt = GNamedCxt ETerm
type Bind = GBind Term
type EBind = GBind ETerm

instance Show (GTerm a) where
    show = show . reify

lift :: Int -> Int -> GTerm a -> GTerm a
lift k n t@(TSort _) = t
lift k n (Pi b t2) = Pi (fmap (lift k n) b) (lift k (n+1) t2)
lift k n t@(Bound m) = if m < n then t else Bound $ m+k
lift k n t@(Free _) = t
lift k n (Lam b u) = Lam (fmap (lift k n) b) (lift k (n+1) u)
lift k n (App t1 t2) = App (lift k n t1) (lift k n t2)
lift k n t@(Meta i m s) = if m < n then t else Meta i (m+k) s

substBound :: Int -> GTerm a -> GTerm a -> GTerm a
substBound i r t@(TSort _) = t
substBound i r (Pi b t2) = Pi (fmap (substBound i r) b) (substBound (i+1) r t2)
substBound i r t@(Bound n) | n < i = t
                           | n == i = lift i 0 r
                           | otherwise = Bound (n-1)
substBound i r t@(Free _) = t
substBound i r (Lam b u) = Lam (fmap (substBound i r) b) (substBound (i+1) r u)
substBound i r (App t1 t2) = App (substBound i r t1) (substBound i r t2)
substBound i r t@(Meta _ _ _) = t
                          
substMeta :: MetaId -> GTerm a -> GTerm a -> GTerm a
substMeta i r t@(TSort _) = t
substMeta i r (Pi b t2) = Pi (fmap (substMeta i r) b) (substMeta i r t2)
substMeta i r t@(Bound _) = t
substMeta i r t@(Free _) = t
substMeta i r (Lam b u) = Lam (fmap (substMeta i r) b) (substMeta i r u)
substMeta i r (App t1 t2) = App (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Meta j _ _) | i == j = r
                             | otherwise = t


subst :: GTerm a -> GTerm a -> GTerm a
subst = substBound 0

isFree_ :: Int -> GTerm a -> Any
isFree_ _ (TSort _) = mempty
isFree_ n (Pi b t2) = foldMap (isFree_ n) b `mappend` isFree_ (n+1) t2
isFree_ n (Bound m) = Any $ n == m
isFree_ _ (Free _) = mempty
isFree_ n (Lam b u) = foldMap (isFree_ n) b `mappend` isFree_ (n+1) u
isFree_ n (App t1 t2) = isFree_ n t1 `mappend` isFree_ n t2

isFree :: Int -> GTerm a -> Bool
isFree n = getAny . isFree_ n


reify t = reify_ (collectFree t) t

freshName :: [Name] -> Name -> Name
freshName xs y | notElem y xs = y
               | otherwise = addSuffix 0
                             where addSuffix n | notElem (y++show n) xs = y++show n
                                               | otherwise = addSuffix (n+1)

collectFree :: GTerm a -> [Name]
collectFree (TSort _) = []
collectFree (Pi b t2) = foldMap collectFree b ++ collectFree t2
collectFree (Bound _) = []
collectFree (Free x) = [x]
collectFree (Lam b t2) = foldMap collectFree b ++ collectFree t2
collectFree (App t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Meta _ _ _) = []

reify_ :: [Name] -> GTerm a -> A.Expr
reify_ xs (TSort Box) = A.TSort noPos A.Box
reify_ xs (TSort Star) = A.TSort noPos A.Star
reify_ xs (Pi (NoBind t1) t2) = A.Pi noPos "" (reify_ xs t1) (reify_ ("":xs) t2)
reify_ xs (Pi (Bind x t1) t2) = A.Pi noPos x' (reify_ xs t1) (reify_ (x':xs) t2)
                                where x' = freshName xs x
reify_ xs (Bound n) = A.Bound noPos n
reify_ xs (Free x) = A.Var noPos x
reify_ xs (Lam (NoBind t) u) = A.Lam noPos "" (reify_ xs t) (reify_ ("":xs) u)
reify_ xs (Lam (Bind x t) u) = A.Lam noPos x' (reify_ xs t) (reify_ (x':xs) u)
                             where x' = freshName xs x
reify_ xs (App t1 t2) = A.App noPos (reify_ xs t1) (reify_ xs t2)
reify_ xs (Meta i _ _) = A.EVar noPos (Just i)

-------- casting

upcast :: GTerm NM -> GTerm EVAR
upcast (TSort s) = TSort s
upcast (Pi b t2) = Pi (fmap upcast b) (upcast t2)
upcast (Bound n) = Bound n
upcast (Free x) = Free x
upcast (Lam b t2) = Lam (fmap upcast b) (upcast t2)
upcast (App t1 t2) = App (upcast t1) (upcast t2)

downcast :: GTerm EVAR -> GTerm NM
downcast (TSort s) = TSort s
downcast (Pi b t2) = Pi (fmap downcast b) (downcast t2)
downcast (Bound n) = Bound n
downcast (Free x) = Free x
downcast (Lam b t2) = Lam (fmap downcast b) (downcast t2)
downcast (App t1 t2) = App (downcast t1) (downcast t2)
downcast (Meta _ _ _) = __IMPOSSIBLE__
