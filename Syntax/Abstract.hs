{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
  ImpredicativeTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
 #-}
{-# LANGUAGE CPP #-}
-- Terms

module Syntax.Abstract where

#include "../undefined.h"
import Utils.Impossible

import Data.Function
import Text.PrettyPrint.HughesPJ

import Syntax.Position


data Sort
    = Box
    | Star
    deriving(Eq)

type Name = String
type IName = String -- inductive type names
type CName = String -- constructor names

data Expr = Ann Pos Expr Expr -- annotated term and type
          | TSort Pos Sort
          | Pi Pos Name Expr Expr -- var name, type, term
          | Bound Pos Int
          | Free Pos Name
          | EVar Pos (Maybe Int)
          | Lam Pos Name Expr Expr -- var name, type, body
          | App Pos Expr Expr

data Command = Definition Name (Maybe Expr) Expr
               | Axiom Name Expr
               | Load FilePath
               | Refine Name Expr Expr


-- show should only be called on closed expressions
-- for open expressions, use ppExpr
instance Show (Expr) where
    show = show . tprint 0 []

ppExpr :: [Name] -> Expr -> String
ppExpr xs = show . tprint 0 xs

type Pos = Position

isFree :: Int -> Expr -> Bool
isFree n (Ann _ t u) = isFree n t || isFree n u
isFree _ (TSort _ _) = False
isFree n (Pi _ _ t1 t2) = isFree n t1 || isFree (n+1) t2
isFree n (Bound _ m) = n == m
isFree _ (Free _ _) = False
isFree _ (EVar _ _) = False
isFree n (Lam _ _ t u) = isFree n t || isFree (n+1) u
isFree n (App _ t1 t2) = isFree n t1 || isFree n t2

-- Pretty printer

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

instance Show Sort where
    show Star = "Prop"
    show Box = "Type"

isPi :: Expr -> Bool
isPi (Pi _ _ _ _) = True
isPi _ = False

isLam :: Expr -> Bool
isLam (Lam _ _ _ _) = True
isLam _ = False

tprint :: Int -> [Name] -> Expr -> Doc
tprint p l (Ann _ t u) = parensIf (p > 1) $ tprint 2 l t <> text " :: " <> tprint 0 l u
tprint _ _ (TSort _ s) = text $ show s
tprint p l t@(Pi _ x t1 t2) | not (isFree 0 t2) = parensIf (p > 0) $ sep [tprint 1 l t1 <> text " ->", tprint 0 (x:l) t2]
                            | otherwise = parensIf (p > 0) $ text "forall " <> nestedPi l t
tprint _ l (Bound _ n) | n < length l = text $ l !! n
                       | otherwise    = __IMPOSSIBLE__
tprint p l t@(Lam _ _ _ _) = parensIf (p > 0) $ text "fun " <> nestedLam l t
tprint _ _ (Free _ x) = text x
tprint _ _ (EVar _ Nothing) = text "_"
tprint _ _ (EVar _ (Just n)) = text $ '?':show n
tprint p l (App _ t1 t2) = parensIf (p > 2) $ sep [tprint 2 l t1, nest 2 $ tprint 3 l t2]

nestedLamDef :: Expr -> ([(Name,Expr)], Expr)
nestedLamDef (Lam _ x t1 t2) = ((x,t1):ds, e)
                               where (ds, e) = nestedLamDef t2
nestedLamDef t = ([], t)

nestedPiDef :: Expr -> ([(Name,Expr)], Expr)
nestedPiDef t@(Pi _ x t1 t2) | not (isFree 0 t2) = ([], t) 
                             | otherwise = ((x,t1):ds, e)
                                           where (ds, e) = nestedPiDef t2
nestedPiDef t = ([], t)

nestedLam :: [Name] -> Expr -> Doc
nestedLam l t = printTyDef l False es <> text " =>" <+> tprint 0 xs r
                where (es, r) = nestedLamDef t
                      xs = reverse (map fst es) ++ l

nestedPi :: [Name] -> Expr -> Doc
nestedPi l t = printTyDef l False es <> text "," <+> tprint 0 xs r
               where (es, r) = nestedPiDef t
                     xs = reverse (map fst es) ++ l

printTyDef :: [Name] -> Bool -> [(Name,Expr)] -> Doc
printTyDef _ _ [] = empty
printTyDef l p ((x,e):es) = parensIf (p || not (null es)) (text (x ++ " : ") <> tprint 0 l e)
                            <+> printTyDef (x:l) True es
