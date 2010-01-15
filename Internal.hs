{-# LANGUAGE TypeSynonymInstances #-}
-- Internal representation of Terms

module Internal where

import Data.Function
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos

import qualified Term as T

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
    deriving(Eq,Show)

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


sortToSort :: T.Sort -> Sort
sortToSort T.Box = Box
sortToSort T.Star = Star

interp :: T.Expr -> Term
interp (T.Ann _ t u) = interp t
interp (T.TSort _ s) = TSort $ sortToSort s
interp (T.Pi _ x t1 t2) = Pi x (interp t1) (interp t2)
interp (T.Bound _ n) = Bound n
interp (T.Free _ x) = Free x
interp (T.Lam _ x t u) = Lam x (interp t) (interp u)
interp (T.App _ t1 t2) = App (interp t1) (interp t2)


-- reify_ :: m T.Expr
-- reify_ (TSort s) = return $ T.TSort s
-- reify_ (Pi x t1 t2) = Pi  

