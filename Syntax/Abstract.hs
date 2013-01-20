{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE FlexibleInstances
  #-}

-- | Abstract syntax returned by the parser.
--
--   We reuse the datatype 'Expr' and related for later phases (in particular,
--   for scope checking). Constructors 'Bound', 'Constr' are not used by
--   the parser.

module Syntax.Abstract where

import Data.Function
import Data.Maybe
import Data.List (intercalate, sortBy)

import Text.PrettyPrint.HughesPJ hiding (comma)

import Syntax.Common
import Syntax.Position
import Syntax.Size

import Utils.Pretty

-- | The main data type of expressions
data Expr =
  Ann Range Expr Expr       -- ^ Annotated term with type, e.g. @ M :: T @
  | Sort Range Sort
  | Pi Range [Bind] Expr    -- ^ Dependent product type.
                            --   e.g. @ forall (x1 ... xn : A), B @
  | Arrow Range Expr Expr   -- ^ Non-dependent product, e.g. @ A -> B @
  | Ident Range Name        -- ^ Identifiers
--  | EVar Range (Maybe Int)  -- ^ existential variable
  | Lam Range [Bind] Expr   -- ^ Abstractions, e.g. @ fun (x1 ... xn : A) => B @
  | App Range Expr Expr     -- ^ Applications
--  | Let Range LetBind Expr
  | Case CaseExpr           -- ^ Case expressions
  | Fix FixExpr             -- ^ Fixpoints

  -- The following constructors are filled by the scope checker, but do not
  -- appear in a correctly parsed expression
  | Bound Range Name Int     -- ^ Bound variables. The name argument is used by
                             -- the pretty printer.
  | Constr Range Name (Name, Int) [Expr] [Expr]
                             -- ^ Constructors are fully applied. Arguments are
                             --
                             -- * Name of the constructor
                             --
                             -- * Name of the inductive type and id of the
                             --   constructor
                             --
                             -- * Parameters (of the inductive type)
                             --
                             -- * Actual arguments of the constructor
  | Ind Range Annot Name
  -- Natural numbers are predefined
  | Number Range Int

-- | Equality on expressions is used by the reifier ("InternaltoAbstract")
--   to join consecutive binds with the same type.

instance Eq Expr where
  (Sort _ s1) == (Sort _ s2) = s1 == s2
  (Pi _ bs1 t1) == (Pi _ bs2 t2) = length bs1 == length bs2 &&
                                   all (uncurry (==)) (zip bs1 bs2) &&
                                   t1 == t2
  (Arrow _ e1 e2) == (Arrow _ e3 e4) = e1 == e3 && e2 == e4
  (Bound _ x1 n1) == (Bound _ x2 n2) = x1 == x2 && n1 == n2
  (Ident _ x1) == (Ident _ x2) = x1 == x2
  (Lam _ bs1 t1) == (Lam _ bs2 t2) = length bs1 == length bs2 &&
                                     all (uncurry (==)) (zip bs1 bs2) &&
                                     t1 == t2
  (App _ e1 e2) == (App _ e3 e4) = e1 == e3 && e2 == e4
  (Ind _ a1 i1) == (Ind _ a2 i2) = a1 == a2 && i1 == i2
  _ == _ = False


data Bind =
  Bind { bindRange :: Range
       , bindImplicit :: Bool
       , bindNames :: [Name]
       , bindExpr  :: Expr
       } -- ^ e.g. @(x y : A)@. List must be non-empty.
         -- Empty name means "_" (See parsing of identifiers)


data CaseExpr = CaseExpr {
  caseRange    :: Range,
  caseArg      :: Expr,         -- ^ Argument of the case
  caseAsName   :: Maybe Name,   -- ^ Bind for the argument in the return type
  caseInName   :: Maybe CaseIn, -- ^ Specification of the subfamily of the
                                -- inductive type of the argument
  caseWhere    :: Maybe Subst,  -- ^ Substitution that unifies the indices of
                                -- the argument and the subfamily given in the
                                -- specification
  caseReturn   :: Maybe Expr,   -- ^ Return type
  caseBranches :: [Branch]
  } deriving(Show)

data CaseIn = CaseIn {
  inRange :: Range,
  inBind  :: [Bind],      -- ^ Variables free in the indices of the subfamily
  inInd   :: Name,        -- ^ The inductive type of the case
  inArgs  :: [Expr]       -- ^ The specification of the subfamily
  } deriving(Show)

data Branch = Branch {
  brRange     :: Range,
  brName      :: Name,
  brConstrId  :: Int,
  brArgsNames :: [Name],
  brBody      :: Expr,
  brSubst     :: Maybe Subst
  } deriving(Show)


newtype Subst = Subst { unSubst :: [Assign] }
                deriving(Show)

data Assign = Assign {
  assgnRange :: Range,
  assgnName :: Name,
  assgnBound :: Int,
  assgnExpr :: Expr
  } deriving(Show)

sortSubst :: Subst -> Subst
sortSubst (Subst sg) = Subst $ sortBy (compare `on` assgnBound) sg


data LetBind = LetBind Range Name (Maybe Expr) Expr
               deriving(Show)

data FixExpr = FixExpr { fixRange :: Range
                       , fixKind  :: InductiveKind
                       , fixNum   :: Int -- only used for fixpoints (not cofixpoints)
                       , fixName  :: Name
                       , fixType  :: Expr
                       , fixBody  :: Expr
                       } deriving(Show)

data Declaration =
  Definition Range Name (Maybe Expr) Expr
  | Assumption Range Name Expr
  | Inductive Range InductiveDef
  | Eval Expr
  | Check Expr (Maybe Expr)
  deriving(Show)

data InductiveDef = InductiveDef
                    { indName   :: Name
                    , indKind   :: InductiveKind
                    , indPars   :: [Parameter]
                    , indType   :: Expr
                    , indConstr :: [Constructor]
                    }


data Constructor = Constructor {
  constrRange :: Range,
  constrName  :: Name,
  constrType  :: Expr,
  constrId    :: Int   -- Not used now. Should be removed
  }


data Parameter =
  Parameter {
    parRange :: Range,
    parNamesPol :: [(Name, Polarity)],
    parType :: Expr
    }


data Sort
    = Type (Maybe Int)
    | Prop
    deriving(Eq)

mkProp, mkType :: Range -> Expr
mkProp r = Sort r Prop
mkType r = Sort r (Type Nothing)

instance Show Sort where
  show Prop = "Prop"
  show (Type (Just n)) = "Type<" ++ show n ++ ">"
  show (Type Nothing)  = "Type"

prettyPrintIndex :: Int -> Doc
prettyPrintIndex = text . map num2Sub . show
  where
    num2Sub c = fromMaybe 'E' (lookup c subTable) -- 'E' should never occur
    subTable = zip ['0'..'9'] ['\x2080'..'\x2089']

instance Pretty Sort where
  prettyPrint Prop = text "Prop"
  prettyPrint (Type (Just n)) = text "Type" <> prettyPrintIndex n
  prettyPrint (Type Nothing)  = text "Type"


declName :: Declaration -> Name
declName (Definition _ x _ _) = x
declName (Assumption _ x _) = x
declName (Inductive _ d) = indName d

buildApp :: Expr -> [Expr] -> Expr
buildApp = foldl (\x y -> App (fuseRange x y) x y)

destroyApp :: Expr -> (Expr, [Expr])
destroyApp (App _ e1 e2) = (func, args ++ [e2])
                           where (func, args) = destroyApp e1
destroyApp e             = (e, [])


-- TODO: print implicit
instance Show Bind where
  show (Bind _ impl x e) = concat ["(", concatMap (++" ") (map show x), " : ", show e, ")"]

instance Eq Bind where
  (Bind _ impl1 xs1 e1) == (Bind _ impl2 xs2 e2) =
    impl1 == impl2 && xs1 == xs2 && e1 == e2


-- | Instances of the class HasNames. This class is used for things that behave
--   like binds

instance HasNames Bind where
  getNames = getNames . bindNames

instance HasNames CaseIn where
  getNames = getNames . inBind

instance HasNames Parameter where
  getNames = getNames . map fst . parNamesPol


instance HasRange Expr where
  getRange (Ann r _ _) = r
  getRange (Sort r _) = r
  getRange (Pi r _ _) = r
  getRange (Arrow r _ _) = r
  getRange (Ident r _) = r
  getRange (Bound r _ _) = r
--  getRange (EVar r _) = r
  getRange (Lam r _ _) = r
  getRange (App r _ _) = r
--  getRange (Let r _ _) = r
  getRange (Case c) = caseRange c
  getRange (Fix f) = fixRange f
  getRange (Constr r _ _ _ _) = r
  getRange (Ind r _ _) = r
  getRange (Number r _) = r

instance HasRange Bind where
  getRange = getRange . bindRange

instance HasRange Constructor where
  getRange (Constructor r _ _ _) = r

instance HasRange Branch where
  getRange = brRange

instance HasRange Subst where
  getRange = getRange . unSubst

instance HasRange Assign where
  getRange = assgnRange

-- | Instances of Show and Pretty. For bound variables, the pretty printer uses
--   the name directly.
--
--   Printing a parsed expression should give the same result modulo comments
--   and whitespaces. In particular, there is no effort in removing unused
--   variable names (e.g., changing @ forall x:A, B @ for @ A -> B @ if @ x @ is
--   not free in @ B @.

-- TODO: print implicit
instance Pretty Bind where
  prettyPrint (Bind _ impl xs e) = ppNames  <+> colon <+> prettyPrint e
    where ppNames = hsep (map prettyPrint xs)

-- TODO:
--  * check precedences
--  * use proper aligment of constructors and branches

instance Pretty Expr where
  prettyPrintDec = pp
    where
      pp :: Int -> Expr -> Doc
      pp n (Ann _ e1 e2) = parensIf (n > 1) $ hsep [pp 2 e1, doubleColon,
                                                    pp 0 e2]
      pp _ (Sort _ s) = prettyPrint s
      pp n (Pi _ bs e) = parensIf (n > 0) $ nestedPi bs e
      pp n (Arrow _ e1 e2) = parensIf (n > 0) $ hsep [pp 1 e1, arrow, pp 0 e2]
      pp _ (Ident _ x) = prettyPrint x -- text $ "[" ++ x ++ "]"
      pp _ (Bound _ x k) = prettyPrint x <> (text $ "[" ++ show k ++ "]") -- text "<" ++ x ">"
--      pp _ (EVar _ Nothing) = text "_"
--      pp _ (EVar _ (Just n)) = char '?' <> int n
      pp n (Lam _ bs e) = parensIf (n > 0) $ nestedLam bs e
      pp n (App _ e1 e2) = parensIf (n > 2) $ hsep [pp 2 e1, pp 3 e2]
      pp n (Case c) = parensIf (n > 0) $ prettyPrint c
      pp n (Fix f) = parensIf (n > 0) $ prettyPrint f
      pp _ (Ind _ a x) = hcat [prettyPrint x, langle, prettyPrint a, rangle]
      pp n (Constr _ x _ pars args) =
        parensIf (n > 2) $ prettyPrint x <+> hsep (map (pp lvl) (pars ++ args))
          where lvl = if length pars + length args == 0 then 0 else 3
      pp _ (Number _ n) = text $ show n

      nestedPi :: [Bind] -> Expr -> Doc
      nestedPi bs e = hsep [text "Π",
                            hsep (map (parens . prettyPrint) bs) <> comma,
                            prettyPrint e]

      nestedLam :: [Bind] -> Expr -> Doc
      nestedLam bs e = hsep [text "λ",
                             hsep (map (parens . prettyPrint) bs), implies]
                       $$ nest 2 (prettyPrint e)

instance Pretty CaseExpr where
  prettyPrint (CaseExpr _ arg asn inn subst ret brs) =
    hsep [maybePPrint ppRet ret, text "case",
          maybePPrint ppAs asn, prettyPrint arg,
          maybePPrint ppIn inn, maybePPrint ppSubst subst,
          text "of"] <+> sep (map (nest 2 . (bar <+>) . prettyPrint) brs)
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
  prettyPrint (Assign _ x _ e) = hsep [prettyPrint x, defEq, prettyPrint e]

instance Pretty Branch where
  prettyPrint (Branch _ x _ args body whSubst) =
    hsep $ prettyPrint x : map prettyPrint args ++ [implies, prettyPrint body]

instance Pretty FixExpr where
  prettyPrint (FixExpr _ k n x tp body) =
    hsep [ppName k, prettyPrint x, colon,
          prettyPrint tp, defEq]
    $$ (nest 2 $ prettyPrint body)
    where ppName I   = text "fix" <> (prettyPrintIndex n)
          ppName CoI = text "cofix"

instance Pretty Declaration where
  prettyPrint (Definition _ x (Just e1) e2) =
    hsep [text "define", prettyPrint x, colon, prettyPrint e1, defEq]
    $$ nest 2 (prettyPrint e2)
  prettyPrint (Definition _ x Nothing e2) =
    hsep [text "define", prettyPrint x, defEq]
    $$ nest 2 (prettyPrint e2)
  prettyPrint (Assumption _ x e) =
    hsep [text "assume", prettyPrint x, colon, prettyPrint e]
  prettyPrint (Inductive _ indDef) = prettyPrint indDef
  prettyPrint (Eval e) =
    hsep [text "eval", prettyPrint e]
  prettyPrint (Check e1 e2) =
    hsep [text "check", prettyPrint e1, prettyPrint e2]

instance Pretty (Maybe Expr) where
  prettyPrint (Just e) = empty <+> colon <+> prettyPrint e
  prettyPrint Nothing = empty

instance Pretty InductiveDef where
  prettyPrint (InductiveDef x k ps e cs) =
    sep $ ind : map (nest 2 . (bar <+>) . prettyPrint) cs
      where ind = hsep [text name, prettyPrint x,
                        hsep (map prettyPrint ps), colon,
                        prettyPrint e, defEq]
            name = case k of
                     I   -> "data"
                     CoI -> "codata"

instance Pretty Parameter where
  prettyPrint (Parameter _ np tp) =
    parens $ hsep [ ppNames, colon, prettyPrint tp ]
      where ppNames = hsep $ map (\(n,p) -> prettyPrint n <+> prettyPrint p) np

instance Pretty Constructor where
  prettyPrint c =
    hsep [prettyPrint (constrName c), colon, prettyPrint (constrType c)]

instance Pretty [Declaration] where
  prettyPrint = vcat . map ((<> dot) . prettyPrint)


instance Pretty [Bind] where
  prettyPrint xs = foldr (\x r -> prettyPrint x <> comma <> r) (text "") xs




------------------------
--- The instances below are used only for debugging

instance Show Expr where
  show (Ann _ e1 e2) = concat [show e1, " :: ", show e2]
  show (Sort _ s) = show s
  show (Pi _ bs e) = concat $ "Pi " : map show bs ++ [", ", show e]
  show (Arrow _ e1 e2) = concat ["(", show e1, ") -> (", show e2, ")"]
  show (Ident _ x) = show x
  show (Lam _ bs e) = concat $ "fun " : map show bs ++ [" => ", show e]
  show (App _ e1 e2) = concat [show e1, " (", show e2, ")"]
  show (Case c) = show c
  show (Fix f) = show f
  show (Bound _ x n) = concat [show x, "[", show n, "]"]
  show (Constr _ x i ps as) = concat $ [show x, show i, "(", intercalate ", " (map show (ps ++ as)), ")"]
  show (Ind _ a x) = concat [show x, "<", show a, ">"]
  show (Number _ n) = show n


instance Show InductiveDef where
  show (InductiveDef name k pars tp constr) =
    concat $ ["Inductive ", show name, " ", show pars, " : ", show tp,
              " := "] ++ map show constr

instance Show Constructor where
  show (Constructor _ name tp _) =
    concat [" | ", show name, " : ", show tp]

instance Show Parameter where
  show (Parameter _ pol tp) = concatMap showNamePol pol ++ ": " ++ show tp
    where showNamePol (x, p) = show x ++ show p ++ " "

