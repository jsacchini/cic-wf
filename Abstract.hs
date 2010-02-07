{-# LANGUAGE GADTs, EmptyDataDecls, TypeOperators, TypeFamilies, RankNTypes,
  ImpredicativeTypes
 #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- Terms

module Abstract where

import Data.Function
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec.Pos

import Position

data Sort
    = Box
    | Star
    deriving(Eq)

type Name = String
type IName = String -- inductive type names
type CName = String -- constructor names


data Expr
    = Ann Pos Expr Expr  -- annotated term and type
    | TSort Pos Sort
    | Pi Pos Name Expr Expr -- var name, type, term
    | Bound Pos Int
    | Free Pos Name
    | Meta Pos Int
    | Lam Pos Name Expr Expr -- var name, type, body
    | App Pos Expr Expr
--    deriving(Show)


{-
data NoMeta
data WithMeta a
data Unknown
data EVar

data FExpr a where
    Ann :: Pos -> FExpr a -> FExpr a -> FExpr a -- annotated term and type
    TSort :: Pos -> Sort -> FExpr a
    Pi :: Pos -> Name -> FExpr a -> FExpr a -> FExpr a -- var name, type, term
    Bound :: Pos -> Int -> FExpr a
    Free :: Pos -> Name -> FExpr a
    Meta :: Pos -> Int -> FExpr (WithMeta EVar)
    EVar :: Pos -> FExpr (WithMeta Unknown)
    Lam :: Pos -> Name -> FExpr a -> FExpr a -> FExpr a -- var name, type, body
    App :: Pos -> FExpr a -> FExpr a -> FExpr a

type Expr = forall a. FExpr a -- (WithMeta EVar)
-}


data Command = Definition Name (Maybe Expr) Expr
             | Axiom Name Expr
             | Load FilePath
             | Refine Name Expr Expr


instance Show Expr where
    show = show . tprint 0 []

type Pos = Position

isFree :: Int -> Expr -> Bool
isFree n (Ann _ t u) = isFree n t || isFree n u
isFree _ (TSort _ _) = False
isFree n (Pi _ x t1 t2) = isFree n t1 || isFree (n+1) t2
isFree n (Bound _ m) = n == m
isFree _ (Free _ _) = False
isFree n (Lam _ x t u) = isFree n t || isFree (n+1) u
isFree n (App _ t1 t2) = isFree n t1 || isFree n t2
isFree n (Meta _ _) = False
-- Pretty printer

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

showboundInt :: [Name] -> Int -> String
showboundInt = (!!)

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
tprint p l (TSort _ s) = text $ show s
tprint p l t@(Pi _ x t1 t2) | not (isFree 0 t2) = parensIf (p > 0) $ sep [tprint 1 l t1 <> text " ->", tprint 0 (x:l) t2]
                            | otherwise = parensIf (p > 0) $ text "forall " <> nestedPi l t
tprint p l (Bound _ n) = text $ showboundInt l n
tprint p l t@(Lam _ x t1 t2) = parensIf (p > 0) $ text "fun " <> nestedLam l t
tprint p l (Free _ x) = text x
tprint p l (App _ t1 t2) = parensIf (p > 2) $ sep [tprint 2 l t1, nest 2 $ tprint 3 l t2]
tprint p l (Meta _ n) = text $ '?':show n

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
