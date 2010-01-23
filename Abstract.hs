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
    | Lam Pos Name Expr Expr -- var name, type, body
    | App Pos Expr Expr
--    deriving(Show)

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

-- Pretty printer

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- class ShowBound a where
--     showbound :: [Name] -> a -> String

showboundInt :: [Name] -> Int -> String
showboundInt = (!!)

-- instance ShowBound Int where
--     showbound = showboundInt

instance Show Sort where
    show Star = "Prop"
    show Box = "Type"

isPi :: Expr -> Bool
isPi (Pi _ _ _ _) = True
isPi _ = False

isLam :: Expr -> Bool
isLam (Lam _ _ _ _) = True
isLam _ = False

-- tprint :: ShowBound a => Int -> [Name] -> Expr a -> Doc
tprint :: Int -> [Name] -> Expr -> Doc
tprint p l (Ann _ t u) = parensIf (p > 1) $ tprint 2 l t <> text " :: " <> tprint 0 l u
tprint p l (TSort _ s) = text $ show s
tprint p l t@(Pi _ x t1 t2) | not (isFree 0 t2) = parensIf (p > 0) $ sep [tprint 1 l t1 <> text " ->", tprint 0 (x:l) t2]
                            | otherwise = parensIf (p > 0) $ text "forall" <> nestedPi l t
tprint p l (Bound _ n) = text $ showboundInt l n
tprint p l t@(Lam _ x t1 t2) = parensIf (p > 0) $ text "fun" <> nestedLam l t
tprint p l (Free _ x) = text x
tprint p l (App _ t1 t2) = parensIf (p > 2) $ sep [tprint 2 l t1, nest 2 $ tprint 3 l t2]

nestedPi :: [Name] -> Expr -> Doc
nestedPi l t@(Pi _ x t1 t2) | not (isFree 0 t2) = text ", " <> tprint 0 l t
	                    | isPi t2 = text " " <> printTyDef l x t1 <> nestedPi (x:l) t2
			    | otherwise = printTyDef l x t1 <> text "," <+> tprint 0 (x:l) t2

nestedLam :: [Name] -> Expr -> Doc
nestedLam l t@(Lam _ x ty u) | isLam u = text " " <> printTyDef l x ty <> nestedLam (x:l) u
                             | otherwise = text " " <> printTyDef l x ty <> text " =>" <+> tprint 0 (x:l) u

printTyDef :: [Name] -> Name -> Expr -> Doc
printTyDef l x t = parens $ text (x ++ " : ") <> tprint 0 l t



