{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs, MultiParamTypeClasses,
  FlexibleContexts, FunctionalDependencies, UndecidableInstances
 #-}
{-# LANGUAGE CPP #-}

-- Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Data.Function
import Data.Foldable hiding (notElem, concat, foldr)
import Data.Monoid

import Syntax.Bind
import Syntax.Name
import Syntax.Position
import qualified Syntax.Abstract as A

import Utils.Misc

data Sort
    = Box
    | Star
    deriving(Eq, Show)

box :: Term
box = TSort Box
star :: Term
star = TSort Star

type MetaId = Int
type Shift = Int
type CxtSize = Int

data Term
    = TSort Sort
    | Pi (Bind Type) Term
    | Bound Int
    | Free Name
    | Lam (Bind Type) Term
    | App Term Term
    | Meta MetaId Shift CxtSize
    | Constr Name (Name, Int) [Term] [Term]
    | Fix Int Name NamedCxt Type Term

type Type = Term

type BindT = Bind Term

type NamedCxt = [Bind Term]

instance Show Term where -- for debugging only
    show = A.ppExpr (take 100 $ bounds 0) . reify
        where bounds n = ("BB "++show n) : bounds (n+1)

ppTerm :: [Name] -> Term -> String
ppTerm xs = A.ppExpr xs . reify

lift :: Int -> Int -> Term -> Term
lift k n t@(TSort _) = t
lift k n (Pi b t2) = Pi (fmap (lift k n) b) (lift k (n+1) t2)
lift k n t@(Bound m) = if m < n then t else Bound $ m+k
lift k n t@(Free _) = t
lift k n (Lam b u) = Lam (fmap (lift k n) b) (lift k (n+1) u)
lift k n (App t1 t2) = App (lift k n t1) (lift k n t2)
lift k n t@(Meta i m s) = if m < n then t else Meta i (m+k) s
lift k n (Constr c x ps as) = Constr c x (map (lift k n) ps) (map (lift k n) as)
lift k n (Fix m x bs t e) = Fix m x (liftCxt (flip lift n) k bs) (lift k (n+cxtSize bs) t) (lift k (n+1) e)

liftCxt :: (Int -> Term -> Term) -> Int -> NamedCxt -> NamedCxt
liftCxt f n [] = []
liftCxt f n (b:bs) = fmap (f n) b : liftCxt f (n+1) bs

subst_ :: Int -> Term -> Term -> Term
subst_ i r t@(TSort _) = t
subst_ i r (Pi b t2) = Pi (fmap (subst_ i r) b) (subst_ (i+1) r t2)
subst_ i r t@(Bound n) | n < i = t
                       | n == i = lift i 0 r
                       | otherwise = Bound (n-1)
subst_ i r t@(Free _) = t
subst_ i r (Lam b u) = Lam (fmap (subst_ i r) b) (subst_ (i+1) r u)
subst_ i r (App t1 t2) = App (subst_ i r t1) (subst_ i r t2)
subst_ i r t@(Meta _ _ _) = t
subst_ i r (Constr c x ps as) = Constr c x (map (subst_ i r) ps) (map (subst_ i r) as)
subst_ i r (Fix n x bs t e) = Fix n x (substCxt_ i r bs) (subst_ (i+cxtSize bs) r t) (subst_ (i+1) r e)

substMeta :: MetaId -> Term -> Term -> Term
substMeta i r t@(TSort _) = t
substMeta i r (Pi b t2) = Pi (fmap (substMeta i r) b) (substMeta i r t2)
substMeta i r t@(Bound _) = t
substMeta i r t@(Free _) = t
substMeta i r (Lam b u) = Lam (fmap (substMeta i r) b) (substMeta i r u)
substMeta i r (App t1 t2) = App (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Meta j _ _) | i == j = r
                             | otherwise = t

subst :: Term -> Term -> Term
subst = subst_ 0

substList_ :: Int -> [Term] -> Term -> Term
substList_ = foldInt subst_

substCxt_ :: Int -> Term -> NamedCxt -> NamedCxt
substCxt_ i r = liftCxt (flip subst_ r) i

substCxt = substCxt_ 0

cxtSubstList_ :: Int -> [Term] -> NamedCxt -> NamedCxt
cxtSubstList_ k bs c = foldr (substCxt_ k) c bs

foldCxt :: (Monoid b) => (Int -> Term -> b) -> Int -> NamedCxt -> b
foldCxt f n [] = mempty
foldCxt f n (b:bs) = foldMap (f n) b `mappend` foldCxt f n bs

isFree_ :: Int -> Term -> Any
isFree_ _ (TSort _) = mempty
isFree_ n (Pi b t2) = foldMap (isFree_ n) b `mappend` isFree_ (n+1) t2
isFree_ n (Bound m) = Any $ n == m
isFree_ _ (Free _) = mempty
isFree_ n (Lam b u) = foldMap (isFree_ n) b `mappend` isFree_ (n+1) u
isFree_ n (App t1 t2) = isFree_ n t1 `mappend` isFree_ n t2
isFree_ n (Constr _ x ps as) = Prelude.foldr mappend mempty (map (isFree_ n) (ps++as))
isFree_ n (Meta _ _ _) = mempty
isFree_ n (Fix _ _ bs t e) = foldCxt isFree_ n bs `mappend` isFree_ (n+cxtSize bs) t `mappend` isFree_ (n+1) e

isFree :: Int -> Term -> Bool
isFree n = getAny . isFree_ n


reify t = reify_ (collectFree t) t

collectFree :: Term -> [Name]
collectFree (TSort _) = []
collectFree (Pi b t2) = foldMap collectFree b ++ collectFree t2
collectFree (Bound _) = []
collectFree (Free x) = [x]
collectFree (Lam b t2) = foldMap collectFree b ++ collectFree t2
collectFree (App t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Meta _ _ _) = []
collectFree (Constr _ x ps as) = concat $ map collectFree (ps ++ as)
collectFree (Fix _ _ bs t e) = concat (map (foldMap collectFree) bs) ++ collectFree t ++ collectFree e

reify_ :: [Name] -> Term -> A.Expr
reify_ xs (TSort Box) = A.TSort noPos A.Box
reify_ xs (TSort Star) = A.TSort noPos A.Star
reify_ xs (Pi (NoBind t1) t2) = A.Pi noPos (NoBind (reify_ xs t1)) (reify_ ("":xs) t2)
reify_ xs (Pi (Bind x t1) t2) = A.Pi noPos (Bind x' (reify_ xs t1)) (reify_ (x':xs) t2)
                                where x' = freshName xs x
reify_ xs (Bound n) = A.Bound noPos n
reify_ xs (Free x) = A.Var noPos x
reify_ xs (Lam (NoBind t) u) = A.Lam noPos (NoBind $ reify_ xs t) (reify_ ("":xs) u)
reify_ xs (Lam (Bind x t) u) = A.Lam noPos (Bind x' (reify_ xs t)) (reify_ (x':xs) u)
                             where x' = freshName xs x
reify_ xs (App t1 t2) = A.App noPos (reify_ xs t1) (reify_ xs t2)
reify_ xs (Meta i _ _) = A.EVar noPos (Just i)
reify_ xs (Constr c x ps as) = A.Constr noPos c x (map (reify_ xs) ps) (map (reify_ xs) as)
reify_ xs (Fix n x bs t e) = A.Fix noPos n x (reifyCxt_ xs bs) (reify_ (xs++map bind bs) t) (reify_ (x:xs) e)

reifyCxt_ xs [] = []
reifyCxt_ xs (NoBind t:bs) = NoBind (reify_ xs t) : reifyCxt_ ("":xs) bs
reifyCxt_ xs (Bind x t:bs) = Bind x' (reify_ xs t) : reifyCxt_ (x':xs) bs
                             where x' = freshName xs x
reifyCxt_ xs (BindDef x t1 t2:bs) = BindDef x' (reify_ xs t1) (reify_ xs t2) : reifyCxt_ (x':xs) bs
                                    where x' = freshName xs x
