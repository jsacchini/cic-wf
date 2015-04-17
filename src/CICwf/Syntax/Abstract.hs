{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
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

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Scoped abstract syntax.

module CICwf.Syntax.Abstract where

import Data.Monoid

import CICwf.Syntax.Common
import CICwf.Syntax.Position


-- | Well-scoped expressions
data Expr
  = Ann Range Expr Expr      -- ^ Annotated term with type, e.g. @ M :: T @
  | Sort Range Sort
  | Pi Range Context Expr    -- ^ Dependent product type.
                             --   e.g. @ forall (x1 ... xn : A), B @
  | Local Range Name         -- ^ Local variables
  | Global Range Name        -- ^ Global assumptions/definitions
  | SApp Range Bool Name SizeExpr
                             -- ^ Sized identifiers
                             --   e.g. nat<i>, listnat<i>
  | Lam Range Context Expr   -- ^ Abstractions, e.g. @ fun (x1 ... xn : A) => B @
  | App Range Expr ArgType Expr  -- ^ Applications
  | Case CaseExpr            -- ^ Case expressions
  | Fix FixExpr Bool              -- ^ Fixpoints
  | Meta Range (Maybe Int)   -- ^ Unspecified terms

  -- The following constructors are filled by the scope checker, but do not
  -- appear in a correctly parsed expression
  | Constr Range Name [Expr]
                             -- ^ Constructors are applied to parameters
                             --
                             -- * Name of the constructor
                             --
                             -- * Parameters (of the inductive type)
  | Ind Range Bool Name SizeExpr [Expr]
                             -- ^ Inductive types are applied to parameters
  -- Well-founded sizes
  | Intro Range (Maybe SizeExpr) Expr
  | CoIntro Range (Maybe (SizeName, SizeExpr)) Expr
  | SizeApp Range Expr (Maybe SizeExpr)


type SizeName = Name

-- | Constrained types
data ConstrExpr
  = ConstrExpr Range [Name] Expr -- ^ Top level type of the form
                                 --   { i j k } -> T
                                 --   where i j k are size variables


data SizeExpr
  = SizeExpr Range Name Int   -- i^n
  | SizeStar Range
  | SizeEmpty
  | SizeInfty
  deriving(Show)


mkApp :: Expr -> [Expr] -> Expr
mkApp = foldl (\x y -> App (fuseRange x y) x explicitArg y)


unApp :: Expr -> (Expr, [Expr])
unApp (App _ e1 _ e2) = (func, args ++ [e2])
  where (func, args)  = unApp e1
unApp e               = (e, [])


mkArrow :: Expr -> Expr -> Expr
mkArrow e1 e2 = Pi noRange (ctxSingle (Bind noRange [noName] (mkArg e1))) e2


unPi :: Expr -> (Context, Expr)
unPi (Pi _ ctx e) = (ctx <> ctx', e')
  where
    (ctx', e') = unPi e
unPi e = (ctxEmpty, e)



mkProp :: Range -> Expr
mkProp r = Sort r Prop

mkType :: Range -> Int -> Expr
mkType r n = Sort r (Type n)


-- | Binds and context

data Bind
  = Bind Range [Name] (Arg Expr)
                     -- ^ e.g. @(x y : A)@. Name list must be non-empty.
  | LetBind Range Name Expr (Arg (Maybe Expr))
                     -- ^ @x := e2 : e1@
  | BindName Range ArgType Name

type Context = Ctx Bind

instance HasNames Bind where
  name (Bind _ x _) = name x

instance SetRange Bind where
  setRange r (Bind _ x y) = Bind r x y

instance HasImplicit Bind where
  isImplicit (Bind _ _ x) = isImplicit x
  modifyImplicit f (Bind r xs i) = Bind r xs (modifyImplicit f i)


mkBind :: Range -> Name -> Bool -> Expr -> Bind
mkBind r x i e = Bind r [x] (modifyImplicit (const i) (mkArg e))

-- | Patterns
data SinglePattern
  = PatternVar Range Name
  | PatternDef Range Name Expr

instance HasNames SinglePattern where
  name (PatternVar _ x)   = name x
  name (PatternDef _ x _) = name x

type Pattern = [SinglePattern]


instance HasRange SinglePattern where
  range (PatternVar r _) = r
  range (PatternDef r _ _) = r

-- | Case expressions

data CaseExpr
  = CaseExpr { caseRange    :: Range
             , caseKind     :: CaseKind (Maybe SizeExpr)
             , caseArg      :: Expr
               -- ^ Argument of the case
             , caseAsName   :: Name
               -- ^ Bind for the argument in the return type
             , caseIndices  :: Maybe IndicesSpec
               -- ^ Specification of the subfamily of the
               -- inductive type of the argument
             , caseReturn   :: Maybe Expr
               -- ^ Return type
             , caseBranches :: [Branch]
             }


data IndicesSpec
  = IndicesSpec { indspecRange :: Range
                , indspecType  :: Name
                  -- ^ The inductive type of the case
                , indspecArgs  :: Pattern
                  -- ^ The subfamily specification
                }

instance HasRange IndicesSpec where
  range = range . indspecRange

data Branch
  = Branch { brRange     :: Range
           , brSize      :: Maybe SizeName
           , brName      :: Name
           , brConstrId  :: Int
           , brArgsNames :: Pattern
           , brBody      :: Expr
           }



instance HasNames IndicesSpec where
  name = name . indspecArgs


-- | (Co-)fix expressions
data FixExpr
  = FixExpr { fixRange :: Range
            , fixKind  :: InductiveKind
            , fixName  :: Name
            , fixSpec  :: FixSpec
            , fixArgs  :: Context
            , fixType  :: Expr
            , fixBody  :: Expr
            }

instance HasNames FixExpr where
  name = (:[]) . fixName


data FixSpec
  = FixStruct Range Int     -- Recursive argument
  | FixPosition Int         -- Position type (types annotated with stars)
  | FixStage Range Name Int -- Recursive size variable


-- | Global declarations

data Declaration
  = Definition Range Name (Maybe ConstrExpr) Expr
  | Assumption Range Name ConstrExpr
  | Inductive Range InductiveDef
  | Eval Expr
  | Check Expr (Maybe Expr)
  | Print Range Name
  | Cofixpoint FixExpr


-- | (Co-)inductive definitions
data InductiveDef
  = InductiveDef { indName       :: Name
                 , indKind       :: InductiveKind
                 , indPars       :: Context
                 , indPolarities :: [Polarity]
                 , indType       :: Expr
                 , indConstr     :: [Constructor]
                 }


-- | Contructors
data Constructor
  = Constructor { constrRange :: Range
                , constrName  :: Name
                , constrType  :: Expr
                }



-- HasRange and SetRange instances

instance HasRange Expr where
  range (Ann r _ _)      = r
  range (Sort r _)       = r
  range (Pi r _ _)       = r
  range (Local r _)      = r
  range (Global r _)     = r
  range (SApp r _ _ _)   = r
  range (Lam r _ _)      = r
  range (App r _ _ _)    = r
  range (Case c)         = range c
  range (Fix f _)        = range f
  range (Meta r _)       = r
  range (Constr r _ _)   = r
  range (Ind r _ _ _ _)  = r
  -- Well-founded sizes
  range (Intro r _ _)    = r
  range (CoIntro r _ _)  = r
  range (SizeApp r _ _)  = r


instance HasRange ConstrExpr where
  range (ConstrExpr r _ _) = r

instance HasRange Bind where
  range (Bind r _ _) = r

instance HasRange CaseExpr where
  range = caseRange

instance HasRange FixExpr where
  range = fixRange

instance SetRange Expr where
  setRange r (Ann _ x y)      = Ann r x y
  setRange r (Sort _ x)       = Sort r x
  setRange r (Pi _ x y)       = Pi r x y
  setRange r (Local _ x)      = Local r x
  setRange r (Global _ x)     = Global r x
  setRange r (Meta _ x)       = Meta r x
  setRange r (Lam _ x y)      = Lam r x y
  setRange r (App _ x t y)    = App r x t y
  setRange r (Case c)         = Case $ setRange r c
  setRange r (Fix f b)        = Fix (setRange r f) b
  setRange r (Constr _ x y)   = Constr r x y
  setRange r (Ind _ b x y z)  = Ind r b x y z
  setRange r (SApp _ x t y)   = SApp r x t y
  setRange r (Intro _ x y)    = Intro r x y
  setRange r (CoIntro _ x y)  = CoIntro r x y
  setRange r (SizeApp _ x y)  = SizeApp r x y


instance SetRange ConstrExpr where
  setRange r (ConstrExpr _ x y) = ConstrExpr r x y

instance SetRange CaseExpr where
  setRange r c = c { caseRange = r }

instance SetRange FixExpr where
  setRange r f = f { fixRange = r }

instance HasRange Constructor where
  range (Constructor r _ _) = r

instance HasRange Branch where
  range = brRange
