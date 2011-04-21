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
import Data.Monoid

import Text.PrettyPrint.HughesPJ

import Syntax.Common
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
  | Arrow Range Expr Expr   -- ^ Non-dependent type
  | Var Range Name
  | Bound Range Name Int    -- ^ name is just a hint
  | EVar Range (Maybe Int)  -- ^ existential variable
  | Lam Range [Bind] Expr   -- ^ var name, type, body
  | App Range Expr Expr
  | Let Range LetBind Expr
  | Case CaseExpr
  | Fix FixExpr
  | Constr Range CName (IName, Int) [Expr] [Expr]
  | Ind Range IName
  deriving(Show) -- for debugging only


buildApp :: Expr -> [Expr] -> Expr
buildApp = foldl (\x y -> App (fuseRange x y) x y)

destroyApp :: Expr -> (Expr, [Expr])
destroyApp (App _ e1 e2) = (func, args ++ [e2])
                           where (func, args) = destroyApp e1
destroyApp e = (e, [])


-- | Equality on expressions is used by the reifier ("InternaltoAbstract")
--   to join consecutive binds with the same type.

instance Eq Expr where
  (Sort _ s1) == (Sort _ s2) = s1 == s2
  (Pi _ bs1 t1) == (Pi _ bs2 t2) = length bs1 == length bs2 &&
                                   all (uncurry (==)) (zip bs1 bs2) &&
                                   t1 == t2
  (Arrow _ e1 e2) == (Arrow _ e3 e4) = e1 == e3 && e2 == e4
  (Bound _ x1 n1) == (Bound _ x2 n2) = x1 == x2 && n1 == n2
  (Var _ x1) == (Var _ x2) = x1 == x2
  (Lam _ bs1 t1) == (Lam _ bs2 t2) = length bs1 == length bs2 &&
                                     all (uncurry (==)) (zip bs1 bs2) &&
                                     t1 == t2
  (App _ e1 e2) == (App _ e3 e4) = e1 == e3 && e2 == e4
  (Ind _ i1) == (Ind _ i2) = i1 == i2
  _ == _ = False

data CaseExpr = CaseExpr {
  caseRange    :: Range,
  caseArg      :: Expr,
  caseAsName   :: Maybe Name,
  caseInName   :: Maybe CaseIn,
  caseWhere    :: Maybe Subst,
  caseReturn   :: Maybe Expr,
  caseBranches :: [Branch]
  } deriving(Show)

data CaseIn = CaseIn {
  inRange :: Range,
  inBind  :: [Bind],
  inInd   :: Name,
  inArgs  :: [Expr]
  } deriving(Show)

data Branch = Branch {
  brRange     :: Range,
  brName      :: CName,
  brConstrId  :: Int,
  brArgsNames :: [Name],
  brBody      :: Expr
  } deriving(Show)

data FixExpr = FixExpr {
   fixRange :: Range,
   fixNum   :: Int,
   fixName  :: Name,
   fixType  :: Expr,
   fixBody  :: Expr
   } deriving(Show)

data Declaration =
  Definition Range Name (Maybe Expr) Expr
  | Assumption Range Name Expr
  -- | Import FilePath
  | Inductive Range IName [Parameter] Expr [Constructor]
  deriving(Show)

declName :: Declaration -> Name
declName (Definition _ x _ _) = x
declName (Assumption _ x _) = x
declName (Inductive _ x _ _ _) = x

data Constructor = Constructor {
  constrRange :: Range,
  constrName  :: CName,
  constrType  :: Expr,
  constrId    :: Int
  } deriving(Show)


data Parameter =
  Parameter {
    parRange :: Range,
    parNamesPol :: [(Name, Polarity)],
    parType :: Expr
    }
  deriving(Show)

instance HasNames Parameter where
  getNames = getNames . map fst . parNamesPol

data Bind =
  Bind { bindRange :: Range,
         bindNames :: [Name],
         bindExpr  :: Expr
       } -- ^ @x y : A@. List must be non-empty
         -- an empty name means "_" (See parser)

instance Show Bind where
  show (Bind _ x e) = concat ["(", concatMap (++" ") (map show x), " : ", show e, ")"]

instance Eq Bind where
  (Bind _ xs1 e1) == (Bind _ xs2 e2) = xs1 == xs2 && e1 == e2

instance HasNames Bind where
  getNames = getNames . bindNames

newtype Subst = Subst { unSubst :: [Assign] }
                deriving(Show)

instance HasRange Subst where
  getRange = getRange . unSubst

data Assign = Assign {
  assgnRange :: Range,
  assgnName :: Name,
  assgnExpr :: Expr
  } deriving(Show)

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
  getRange (Case c) = caseRange c
  getRange (Fix f) = fixRange f
  getRange (Constr r _ _ _ _) = r
  getRange (Ind r _) = r

instance HasRange Bind where
  getRange (Bind r _ _) = r

instance HasRange Constructor where
  getRange (Constructor r _ _ _) = r

instance HasRange Branch where
  getRange = brRange

instance HasRange Assign where
  getRange = assgnRange

-- | Instances of Show and Pretty. For bound variables, the pretty printer will
--   use the name contained as a hint directly.

instance Show Sort where
  show Prop = "Prop"
  show (Type n) = "Type" ++ show n

instance Pretty Sort where
  prettyPrint = text . show


instance Pretty Bind where
  prettyPrint (Bind _ xs e) = ppNames  <+> colon <+> prettyPrint e
                              where ppNames = hsep (map prettyPrint xs)

instance Pretty Expr where
  prettyPrintDec = pp
    where
      pp :: Int -> Expr -> Doc
      pp n (Ann _ e1 e2) = parensIf (n > 1) $ hsep [pp 2 e1, doubleColon,
                                                    pp 0 e2]
      pp _ (Sort _ s) = prettyPrint s
      pp n (Pi _ bs e) = parensIf (n > 0) $ nestedPi bs e
      pp n (Arrow _ e1 e2) = parensIf (n > 0) $ hsep [pp 1 e1, arrow, pp 0 e2]
      pp _ (Var _ x) = prettyPrint x -- text $ "[" ++ x ++ "]"
      pp _ (Bound _ x _) = prettyPrint x -- text "<" ++ x ">"
      pp _ (EVar _ Nothing) = text "_"
      pp _ (EVar _ (Just n)) = char '?' <> int n
      pp n (Lam _ bs e) = parensIf (n > 0) $ nestedLam bs e
      pp n (App _ e1 e2) = parensIf (n > 2) $ hsep [pp 2 e1, pp 3 e2]
      -- pp p l (Constr _ x _ ps as) = parensIf (p > 2) $ text x <+> foldr (<+>) empty (map (pp p l) (ps ++ as))
      pp n (Case c) = parensIf (n > 0) $ prettyPrint c
      pp n (Fix f) = parensIf (n > 0) $ prettyPrint f
      pp _ e = text $ concat ["* ", show e, " *"]

      nestedPi :: [Bind] -> Expr -> Doc
      nestedPi bs e = hsep [text "forall",
                            hsep (map (parens . prettyPrint) bs) <> comma,
                            prettyPrint e]

      nestedLam :: [Bind] -> Expr -> Doc
      nestedLam bs e = hsep [text "fun",
                             hsep (map (parens . prettyPrint) bs), implies,
                             prettyPrint e]

instance Pretty CaseExpr where
  prettyPrint (CaseExpr _ arg asn inn subst ret brs) =
    hsep [maybePPrint ppRet ret, text "case",
          maybePPrint ppAs asn, prettyPrint arg,
          maybePPrint ppIn inn, maybePPrint ppSubst subst,
          text "of", hsep $ map (nest 2 . (bar <+>) . prettyPrint) brs]
      where
        ppRet r   = hsep [langle, prettyPrint r, rangle]
        ppAs a    = hsep [prettyPrint a, defEq]
        ppIn i    = hsep [text "in", prettyPrint i]
        ppSubst s | null (unSubst s) = empty
                  | otherwise        = text "where" <+> prettyPrint s

instance Pretty CaseIn where
  prettyPrint (CaseIn _ bs i args) =
    hsep $ context ++ [prettyPrint i] ++ map prettyPrint args
      where
        context | null bs   = [empty]
                | otherwise = lbrack : map (parens . prettyPrint) bs ++ [rbrack]

instance Pretty Subst where
  prettyPrint = hsep . map (parens . prettyPrint) . unSubst

instance Pretty Assign where
  prettyPrint (Assign _ x e) = hsep [prettyPrint x, defEq, prettyPrint e]

instance Pretty Branch where
  prettyPrint (Branch _ x id args body) =
    hsep $ prettyPrint x : map prettyPrint args ++ [implies, prettyPrint body]

instance Pretty FixExpr where
  prettyPrint (FixExpr _ n x tp body) =
    hsep [text "fix" <> int n, prettyPrint x, colon, prettyPrint tp,
          defEq, prettyPrint body]

instance Pretty Declaration where
  prettyPrint (Definition _ x (Just e1) e2) =
    hsep [text "define", prettyPrint x, colon, prettyPrint e1, defEq, prettyPrint e2]
  prettyPrint (Definition _ x Nothing e2) =
    hsep [text "define", prettyPrint x, defEq, prettyPrint e2]
  prettyPrint (Assumption _ x e) =
    hsep [text "assume", prettyPrint x, colon, prettyPrint e]
  prettyPrint (Inductive _ x ps e cs) =
    sep $ indName : map (nest 2 . (bar <+>) . prettyPrint) cs
      where indName = hsep [text "data", prettyPrint x,
                            hsep (map prettyPrint ps), colon,
                            prettyPrint e, defEq]

instance Pretty Parameter where
  prettyPrint (Parameter _ np tp) =
    parens $ hsep [ ppNames, colon, prettyPrint tp ]
      where ppNames = hsep $ map (\(n,p) -> prettyPrint n <+> prettyPrint p) np

instance Pretty Constructor where
  prettyPrint c =
    hsep [prettyPrint (constrName c), colon, prettyPrint (constrType c)]

instance Pretty [Declaration] where
  prettyPrint = vcat . map ((<> dot) . prettyPrint)
