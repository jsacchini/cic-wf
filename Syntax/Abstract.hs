{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
  ImpredicativeTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
 #-}
{-# LANGUAGE CPP #-}
-- Terms

module Syntax.Abstract where

#include "../undefined.h"
import Utils.Impossible

import Data.Function
import Data.Foldable hiding (notElem)
import Data.Monoid
import Text.PrettyPrint.HughesPJ

import Syntax.Bind
import Syntax.Name
import Syntax.Position

data Sort
    = Box
    | Star
    deriving(Eq)

type IName = String -- inductive type names
type CName = String -- constructor names

type Pos = Position

data Expr = Ann Pos Expr Expr -- annotated term and type
          | TSort Pos Sort
          | Pi Pos BindE Expr -- var name, type, term
          | Var Pos Name
          | Bound Pos Int
          | EVar Pos (Maybe Int)
          | Lam Pos BindE Expr -- var name, type, body
          | App Pos Expr Expr
          | Match Pos MatchExpr
          | Fix Pos Int Name [BindE] Expr Expr
          | Constr Pos (IName, Int) [Expr] [Expr]
          | Ind Pos IName [Expr]
          deriving(Show) -- for debugging only
-- instance Show (Expr) where
--     show = show . tprint 0 []

type BindE = Bind Expr

data MatchExpr = MkMatch {
      matchArg :: Expr,
      asName :: Maybe Name,
      inName :: Maybe (IName, [Name]),
      matchRet :: Maybe Expr,
      branches :: [Branch]
    } deriving(Show)
data Branch = MkBranch {
--      branchPos :: Pos,
      branchName :: CName,
      constrNumber :: Int,
      argNames :: [Name],
      branchBody :: Expr
    } deriving(Show)

data IndExpr = MkInd {
      indName :: Name,
      indParams :: [BindE],
      indArg :: Expr,
      indConstr :: [ConstrExpr]
    } deriving(Show)
data ConstrExpr = MkConstrExpr {
      constrName :: Name,
      constrType :: Expr
    } deriving(Show)

data Command = Definition Name (Maybe Expr) Expr
             | AxiomCommand Name Expr
             | Load FilePath
             -- | Refine Name Expr Expr
             | Inductive IndExpr
             deriving(Show)

type Param = Expr
type Arg = Expr

-- show should only be called on closed expressions
-- for open expressions, use ppExpr

ppExpr :: [Name] -> Expr -> String
ppExpr xs = show . tprint 0 xs
-- ppExpr _ = show

isFree_ :: Int -> Expr -> Any
isFree_ n (Ann _ t u) = isFree_ n t `mappend` isFree_ n u
isFree_ _ (TSort _ _) = mempty
isFree_ n (Pi _ t1 t2) = foldMap (isFree_ n) t1 `mappend` isFree_ (n+1) t2
isFree_ n (Bound _ m) = Any $ n == m
isFree_ _ (Var _ _) = mempty
isFree_ _ (EVar _ _) = mempty
isFree_ n (Lam _ t u) = foldMap (isFree_ n) t `mappend` isFree_ (n+1) u
isFree_ n (App _ t1 t2) = isFree_ n t1 `mappend` isFree_ n t2

isFree n = getAny . isFree_ n
-- Pretty printer

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

instance Show Sort where
    show Star = "Prop"
    show Box = "Type"

isPi :: Expr -> Bool
isPi (Pi _ _ _) = True
isPi _ = False

isLam :: Expr -> Bool
isLam (Lam _ _ _) = True
isLam _ = False

tprint :: Int -> [Name] -> Expr -> Doc
tprint p l (Ann _ t u) = parensIf (p > 1) $ tprint 2 l t <> text " :: " <> tprint 0 l u
tprint _ _ (TSort _ s) = text $ show s
tprint p l t@(Pi _ b t2) | not (isFree 0 t2) = parensIf (p > 0) $ sep [tprint 1 l t1 <> text " ->", tprint 0 (x:l) t2]
                         | otherwise = parensIf (p > 0) $ text "forall " <> nestedPi l t
    where (x,t1) = (bind b, expr b)
tprint p l t@(Lam _ _ _) = parensIf (p > 0) $ text "fun " <> nestedLam l t
tprint _ l (Bound _ n) | n < length l = text (l !! n)
                       | otherwise = __IMPOSSIBLE__
tprint _ _ (Var _ x) = text "[" <> text x <> text "]"
tprint _ _ (EVar _ Nothing) = text "_"
tprint _ _ (EVar _ (Just n)) = text $ '?':show n
tprint p l (App _ t1 t2) = parensIf (p > 2) $ sep [tprint 2 l t1, nest 2 $ tprint 3 l t2]

nestedLamDef :: Expr -> ([(Name,Expr)], Expr)
nestedLamDef (Lam _ b t2) = ((varName,t1):ds, e)
                            where (ds, e) = nestedLamDef t2
                                  varName | isFree 0 t2 = x
                                          | otherwise = "_"
                                  (x,t1) = (bind b, expr b)
nestedLamDef t = ([], t)

nestedPiDef :: Expr -> ([(Name,Expr)], Expr)
nestedPiDef t@(Pi _ b t2) | not (isFree 0 t2) = ([], t)
                          | otherwise = ((x,t1):ds, e)
    where (ds, e) = nestedPiDef t2
          (x,t1) = (bind b, expr b)
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
