{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
  TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
 #-}
{-# LANGUAGE CPP #-}

-- Abstract syntax
-- The parser returns an abstract tree
-- It is also reused by the scope checker
-- Bound, Ind, Constr are filled by the scope checker

module Syntax.Abstract where

#include "../undefined.h"
import Utils.Impossible

import Data.Function
import Data.Foldable hiding (notElem, concat, foldr)
import Data.Monoid
import Text.PrettyPrint.HughesPJ

import Syntax.Name
import Syntax.Position

data Sort
    = Type Int
    | Prop
    deriving(Eq)

instance Show Sort where
  show Prop = "Prop"
  show (Type n) = "Type" ++ show n

type IName = String -- inductive type names
type CName = String -- constructor names

data Expr = Ann Range Expr Expr -- annotated term with type
          | Sort Range Sort
          | Pi Range [Bind] Expr -- var name, type, term
          | Var Range Name
          | Bound Range Int
          | EVar Range (Maybe Int)  -- existential variable
          | Lam Range [Bind] Expr -- var name, type, body
          | App Range Expr Expr
          | Let Range LetBind Expr
          | Match Range MatchExpr
          | Fix Range Int Name Telescope Expr Expr
          | Constr Range CName (IName, Int) [Expr] [Expr]
          | Ind Range IName
          deriving(Show) -- for debugging only
-- instance Show (Expr) where
--     show = show . tprint 0 []

data MatchExpr = MkMatch {
  matchRange    :: Range,
  matchArg      :: Expr,
  matchAsName   :: Maybe Name,
  matchInName   :: Maybe (IName, [Name]),
  matchReturn   :: Maybe Expr,
  matchBranches :: [Branch]
  } deriving(Show)

data Branch = Branch {
  brRange     :: Range,
  brName      :: CName,
  brConstrId  :: Int,
  brArgsNames :: [Name],
  brBody      :: Expr
  } deriving(Show)

data Declaration = Definition Range Name (Maybe Expr) Expr
                 | Axiom Range Name Expr
                 | Import FilePath
                 | Inductive Range IName Parameters Expr [Constructor]
                 deriving(Show)

data Constructor = Constructor {
  constrRange :: Range,
  constrName  :: CName,
  constrType  :: Expr,
  constrId    :: Int
  } deriving(Show)


type Parameters = Telescope

data Bind = Bind Range [Name] Expr       -- x y : A. List must be non-empty
          | NoBind Expr                  -- _ : A. We use the Range of expr
          -- | BindDef Range Name Expr Expr
          deriving(Show)


type Telescope = [Bind]

data LetBind = LetBind Range Name (Maybe Expr) Expr
               deriving(Show)

instance HasRange Expr where
  getRange (Ann r _ _) = r
  getRange (Sort r _) = r
  getRange (Var r _) = r
  getRange (Bound r _) = r
  getRange (EVar r _) = r
  getRange (Lam r _ _) = r
  getRange (App r _ _) = r
  getRange (Let r _ _) = r
  getRange (Match r _) = r
  getRange (Fix r _ _ _ _ _) = r
  getRange (Constr r _ _ _ _) = r
  getRange (Ind r _) = r

instance HasRange Bind where
  getRange (Bind r _ _) = r
  getRange (NoBind e) = getRange e

instance HasRange Constructor where
  getRange (Constructor r _ _ _) = r

{-
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
isFree_ n (Constr _ _ _ ps as) = foldr mappend mempty (map (isFree_ n) (ps++as))
isFree_ n (Fix _ _ _ bs t e) = foldr mappend mempty (map (foldMap (isFree_ n)) bs) `mappend` isFree_ n t `mappend` isFree_ n e

isFree n = getAny . isFree_ n
-- Pretty printer

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

instance Show Sort where
    show Prop = "Prop"
    show (Type n) = "Type" ++ show n

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
                       | otherwise = text $ "PROBLEM " ++ show n
tprint _ _ (Var _ x) = text x -- text "[" <> text x <> text "]"
tprint _ _ (EVar _ Nothing) = text "_"
tprint _ _ (EVar _ (Just n)) = text $ '?':show n
tprint p l (App _ t1 t2) = parensIf (p > 2) $ sep [tprint 2 l t1, nest 2 $ tprint 3 l t2]
tprint p l (Constr _ x _ ps as) = parensIf (p > 2) $ text x <+> foldr (<+>) empty (map (tprint p l) (ps ++ as))
tprint _ _ t = text $ concat ["* ", show t, " *"]

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

-}