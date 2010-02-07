{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE CPP #-}

module Refiner.Internal where

-- Internal representation of Terms

import Data.Function
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos

import Position
import qualified Abstract as A

data Sort 
    = Box
    | Star
    deriving(Eq, Show)

type Name = String

type MetaId = Int
type Shift = Int
type CxtSize = Int

data Term
    = TSort Sort
    | Pi Name Type Term
    | Bound Int
    | Free Name
    | Lam Name Type Term
    | App Term Term
    | Meta MetaId Shift CxtSize
    deriving(Eq)

instance Show Term where
    show = show . reify

type Type = Term

lift :: Int -> Int -> Term -> Term
lift k n t@(TSort _) = t
lift k n (Pi x t1 t2) = Pi x (lift k n t1) (lift k (n+1) t2)
lift k n t@(Bound m) = if m < n then t else Bound $ m+k
lift k n t@(Free _) = t
lift k n (Lam x t u) = Lam x (lift k n t) (lift k (n+1) u)
lift k n (App t1 t2) = App (lift k n t1) (lift k n t2)
lift k n t@(Meta i m c) = if m < n then t else Meta i (m+k) c

subst_ :: Int -> Term -> Term -> Term
subst_ i r t@(TSort _) = t
subst_ i r (Pi x t1 t2) = Pi x (subst_ i r t1) (subst_ (i+1) r t2)
subst_ i r t@(Bound n) | n < i = t
                       | n == i = lift i 0 r
		       | otherwise = Bound (n-1)
subst_ i r t@(Free _) = t
subst_ i r (Lam x t u) = Lam x (subst_ i r t) (subst_ (i+1) r u)
subst_ i r (App t1 t2) = App (subst_ i r t1) (subst_ i r t2)
subst_ i r t@(Meta _ _ _) = t


subst :: Term -> Term -> Term
subst = subst_ 0

substMeta :: MetaId -> Term -> Term -> Term
substMeta i r t@(TSort _) = t
substMeta i r (Pi x t1 t2) = Pi x (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Bound _) = t
substMeta i r t@(Free _) = t
substMeta i r (Lam x t u) = Lam x (substMeta i r t) (substMeta i r u)
substMeta i r (App t1 t2) = App (substMeta i r t1) (substMeta i r t2)
substMeta i r t@(Meta j _ _) | i == j = r
                             | otherwise = t
 

multisubst :: Int -> [Term] -> Term -> Term
multisubst i ts u = snd $ foldl (\(i, t) r -> (i+1, subst_ i r t)) (i, u) ts

mapsubst :: Int -> Term -> [Term] -> [Term]
mapsubst n t [] = []
mapsubst n t (u:us) = subst_ n t u : mapsubst (n+1) t us

isFree :: Int -> Term -> Bool
isFree _ (TSort _) = False
isFree n (Pi _ t1 t2) = isFree n t1 || isFree (n+1) t2
isFree n (Bound m) = n == m
isFree _ (Free _) = False
isFree n (Lam _ t u) = isFree n t || isFree (n+1) u
isFree n (App t1 t2) = isFree n t1 || isFree n t2
isFree n (Meta _ m _) = n == m

class Interp a where
    interp :: a -> Term

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
    interp (A.Meta _ n) = Meta n 0 0

class Reify a where
    reify :: a -> A.Expr

instance Reify Sort where
    reify Box = A.TSort noPos A.Box
    reify Star = A.TSort noPos A.Star


instance Reify Term where
    reify t = reify_ (collectFree t) t

freshName :: [Name] -> Name -> Name
freshName xs y | not (elem y xs) = y
               | otherwise = addSuffix 0
                             where addSuffix n | not (elem (y++show n) xs) = y++show n
                                               | otherwise = addSuffix (n+1)

collectFree :: Term -> [Name]
collectFree (TSort _) = []
collectFree (Pi _ t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Bound _) = []
collectFree (Free x) = [x]
collectFree (Lam _ t1 t2) = collectFree t1 ++ collectFree t2
collectFree (App t1 t2) = collectFree t1 ++ collectFree t2
collectFree (Meta _ _ _) = []

reify_ :: [Name] -> Term -> A.Expr
reify_ xs (TSort s) = reify s
reify_ xs (Pi x t1 t2) = A.Pi noPos x' (reify_ xs t1) (reify_ (x:xs) t2)
                         where x' = freshName xs x
reify_ xs (Bound n) = A.Bound noPos n
reify_ xs (Free x) = A.Free noPos x
reify_ xs (Lam x t u) = A.Lam noPos x' (reify_ xs t) (reify_ (x:xs) u)
                        where x' = freshName xs x
reify_ xs (App t1 t2) = A.App noPos (reify_ xs t1) (reify_ xs t2)
reify_ xs (Meta x _ _) = A.Meta noPos x



-- data Global
--     = Def Type Term
-- --    | Ind NamedCxt NamedCxt Sort [ConstrType]
--     | Axiom Type
--    deriving(Show)

-- class (Monad m) => MonadGE m where
--     lookupGE :: Name -> m Global

