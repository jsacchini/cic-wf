{-# LANGUAGE TypeSynonymInstances #-}
-- Internal representation of Terms

module Internal where

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

data Term
    = TSort Sort
    | Pi Name Type Term
    | Bound Int
    | Free Name
    | Lam Name Type Term
    | App Term Term
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

subst_ :: Int -> Term -> Term -> Term
subst_ i r t@(TSort _) = t
subst_ i r (Pi x t1 t2) = Pi x (subst_ i r t1) (subst_ (i+1) r t2)
subst_ i r t@(Bound n) | n < i = t
                       | n == i = lift i 0 r
		       | otherwise = Bound (n-1)
subst_ i r t@(Free _) = t
subst_ i r (Lam x t u) = Lam x (subst_ i r t) (subst_ (i+1) r u)
subst_ i r (App t1 t2) = App (subst_ i r t1) (subst_ i r t2)

subst :: Term -> Term -> Term
subst = subst_ 0

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

class Reify a where
    reify :: a -> A.Expr

instance Reify Sort where
    reify Box = A.TSort noPos A.Box
    reify Star = A.TSort noPos A.Star


-- TODO: change names of bound variables if they clash (needs environment)
instance Reify Term where
    reify (TSort s) = reify s
    reify (Pi x t1 t2) = A.Pi noPos x (reify t1) (reify t2)
    reify (Bound n) = A.Bound noPos n
    reify (Free x) = A.Free noPos x
    reify (Lam x t u) = A.Lam noPos x (reify t) (reify u)
    reify (App t1 t2) = A.App noPos (reify t1) (reify t2)


