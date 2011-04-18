{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
  TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
 #-}
{-# LANGUAGE CPP #-}

-- | Abstract syntax returned by the parser.
-- It is also reused by the scope checker;
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

import Utils.Pretty

data Sort
    = Type Int
    | Prop
    deriving(Eq)

type IName = Name -- ^ inductive type names
type CName = Name -- ^ constructor names

-- | The main data type of expressions
data Expr =
  Ann Range Expr Expr       -- ^ annotated term with type
  | Sort Range Sort
  | Pi Range [Bind] Expr    -- ^ Dependent type. var name, type, term
  | Arrow Range Expr Expr         -- ^ Non-dependent type
  | Var Range Name
  | Bound Range Name Int    -- ^ name is just a hint
  | EVar Range (Maybe Int)  -- ^ existential variable
  | Lam Range [Bind] Expr   -- ^ var name, type, body
  | App Range Expr Expr
  | Let Range LetBind Expr
  | Match Range MatchExpr
  | Fix Range Int Name Telescope Expr Expr
  | Constr Range CName (IName, Int) [Expr] [Expr]
  | Ind Range IName
  deriving(Show) -- for debugging only

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
                 | Assumption Range Name Expr
                 | Import FilePath
                 | Inductive Range IName Parameters Expr [Constructor]
                 deriving(Show)

instance HasName Declaration where
  getName (Definition _ x _ _) = x
  getName (Assumption _ x _) = x
  getName (Inductive _ x _ _ _) = x
  getName (Import _) = error "to be implemented (getName Import)"

data Constructor = Constructor {
  constrRange :: Range,
  constrName  :: CName,
  constrType  :: Expr,
  constrId    :: Int
  } deriving(Show)

instance HasNames Constructor where
  getNames c = [constrName c]


type Parameters = Telescope

data Bind = Bind Range [Name] Expr       -- ^ @x y : A@. List must be non-empty
                                         -- an empty name means "_" (See parser)
          | NoBind Expr                  -- _ : A. We use the Range of expr
          -- BindDef Range Name Expr Expr
          deriving(Show)

instance HasNames Bind where
  getNames (Bind _ xs _) = xs
  getNames (NoBind _) = ["_"]

type Telescope = [Bind]

data LetBind = LetBind Range Name (Maybe Expr) Expr
               deriving(Show)

instance HasRange Expr where
  getRange (Ann r _ _) = r
  getRange (Sort r _) = r
  getRange (Pi r _ _) = r
  getRange (Var r _) = r
  getRange (Bound r _ _) = r
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


-- Instances of Show and Pretty
-- For bound variables, the pretty printer will use the name contained as a hint
-- directly.
-- Functions uniqNames and uniqNamesList can be used to turn hints in bound
-- names into unique names
-- show should only be called on closed expressions
-- for open expressions, use ppExpr

instance Show Sort where
  show Prop = "Prop"
  show (Type n) = "Type" ++ show n

instance Pretty Sort where
  prettyPrint = text . show

instance Pretty Name where
  prettyPrint xs | null xs   = text "_"
                 | otherwise = text xs


instance Pretty Bind where
  prettyPrint (Bind _ xs e) = ppNames  <+> colon <+> prettyPrint e
                              where ppNames = hsep (map prettyPrint xs)
  prettyPrint (NoBind e) = text "_" <+> colon <+> prettyPrint e

instance Pretty Expr where
  prettyPrintDec = pp
    where
      pp :: Int -> Expr -> Doc
      pp n (Ann _ e1 e2) = parensIf (n > 1) $ pp 2 e1 <+> doubleColon <+> pp 0 e2
      pp _ (Sort _ s) = prettyPrint s
      pp n (Pi _ bs e) = parensIf (n > 0) $ nestedPi bs e
      pp _ (Var _ x) = text x -- text $ "[" ++ x ++ "]"
      pp _ (Bound _ x _) = text x -- text "<" ++ x ">"
      pp _ (EVar _ Nothing) = text "_"
      pp _ (EVar _ (Just n)) = char '?' <> int n
      pp n (Lam _ bs e) = parensIf (n > 0) $ nestedLam bs e
      pp n (App _ e1 e2) = parensIf (n > 2) $ hsep [pp 2 e1, pp 3 e2]
      -- pp p l (Constr _ x _ ps as) = parensIf (p > 2) $ text x <+> foldr (<+>) empty (map (pp p l) (ps ++ as))
      pp _ e = text $ concat ["* ", show e, " *"]

      nestedPi :: [Bind] -> Expr -> Doc
      nestedPi bs e = text "forall" <+> hsep (map (parens . prettyPrint) bs) <> comma <+> prettyPrint e

      nestedLam :: [Bind] -> Expr -> Doc
      nestedLam bs e = text "fun" <+> hsep (map (parens . prettyPrint) bs) <+> implies <+> prettyPrint e

instance Pretty Declaration where
  prettyPrint (Definition _ x (Just e1) e2) =
    hsep [text "define", text x, colon, prettyPrint e1, defEq, prettyPrint e2]
  prettyPrint (Definition _ x Nothing e2) =
    hsep [text "define", text x, defEq, prettyPrint e2]
  prettyPrint (Assumption _ x e) =
    hsep [text "assume", text x, colon, prettyPrint e]
  prettyPrint (Inductive _ x ps e cs) =
    sep $ indName : map (nest 2 . (bar <+>) . prettyPrint) cs
      where indName = hsep [text "data", text x, sep (map (parens . prettyPrint) ps), colon, prettyPrint e, defEq]
instance Pretty Constructor where
  prettyPrint c =
    hsep [text (constrName c), colon, prettyPrint (constrType c)]

instance Pretty [Declaration] where
  prettyPrint = vcat . map ((<> dot) . prettyPrint)
