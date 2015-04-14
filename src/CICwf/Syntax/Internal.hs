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

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards              #-}

-- | Internal representation of Terms

module CICwf.Syntax.Internal where

import qualified Data.Foldable       as Fold
import           Data.Maybe
import           Data.Monoid
import           Data.Set            (Set)
import qualified Data.Set            as Set

import           CICwf.Syntax.Common

import           CICwf.Utils.Misc
import           CICwf.Utils.Pretty hiding ((<>))
import           CICwf.Utils.Sized


------------------------------------------------------------
-- * Size annotations for (co-)inductive types
------------------------------------------------------------

-- data Annot
--   = Empty             -- ^ No annotation (for bare terms);
--   | SBound Int        -- ^ For position types (in definition of (co-)fixpoints;
--   | Size Size         -- ^ An actual size annotation.

-- | Meta variables

type SizeName = Name

newtype StageVar = SVar Int
                   deriving(Eq, Enum, Num, Ord)

instance Show StageVar where
  show (SVar k) = 'α' : show k


data Stage
  = StageVar StageVar Int
  | Infty
  deriving(Eq, Ord)

instance Show Stage where
  show Infty = "∞"
  show (StageVar s n) = show s ++ (if n > 0 then "+" ++ show n else "")

data Annot
  = Empty
  | Star
  | Stage Stage
  | SizeVar Name Int
  deriving(Eq, Ord)

instance Show Annot where
  show Empty = "o"
  show Star = "*"
  show (Stage s) = show s
  show (SizeVar x n) = show x ++ (if n > 0 then "+" ++ show n else "")

instance Pretty Annot where
  pretty = text . show

  -- | StageVar StageVar Int
  -- | SBound Int

class MkAnnot a where
  mkAnnot :: a -> Annot
  destAnnot :: Annot -> Maybe a

instance MkAnnot StageVar where
  mkAnnot s = Stage (StageVar s 0)
  destAnnot = sbase

instance MkAnnot Name where
  mkAnnot s = SizeVar s 0
  destAnnot = nbase


infty :: Annot
infty = Stage Infty

isInfty :: Annot -> Bool
isInfty (Stage Infty) = True
isInfty _ = False



hat :: Annot -> Annot
hat (Stage (StageVar s n)) = Stage (StageVar s (n+1))
hat (SizeVar s n) = SizeVar s (n+1)
hat s = s

hatn :: Int -> Annot -> Annot
hatn m (Stage (StageVar s n)) = Stage (StageVar s (n+m))
hatn m (SizeVar s n) = SizeVar s (n+m)
hatn _ s = s

sbase :: Annot -> Maybe StageVar
sbase (Stage (StageVar s _)) = Just s
sbase _ = Nothing

nbase :: Annot -> Maybe Name
nbase (SizeVar x _) = Just x
nbase _ = Nothing

baseAnnot :: Annot -> Maybe Annot
baseAnnot (SizeVar x _) = Just $ SizeVar x 0
baseAnnot (Stage (StageVar s _)) = Just $ Stage (StageVar s 0)
baseAnnot _ = Nothing

-- instance Eq Annot where
--   Empty     == Empty     = True
--   SBound n1 == SBound n2 = True
--   Size s1   == Size s2   = s1 == s2
--   _         == _         = False

-- instance Show Annot where
--   show Empty =  ""
--   show (SBound n)  = show n
--   show (Size s) = show s


------------------------------------------------------------
-- * Internal term representation
------------------------------------------------------------

data Term
  = Sort Sort
  | Pi Context Term
  | Bound Int
  | Var Name
  | SIdent Name Annot  -- Sized identifier, e.g. nat<i>, listnat<i+1>
  | Lam Context Term
  | App Term [Term]
  | Meta MetaVar
  | Constr Name (Name, Int) [Term] -- Constructors are applied to parameters
  | Fix FixTerm
  | Case CaseTerm
  | Ind Annot Bool Name [Term]  -- Inductive types are applied to parameters
  -- Well-founded sizes
  | Intro Annot Term
  | CoIntro SizeName Annot Term
  | SizeApp Term Annot
  | Subset SizeName Annot Type -- [ ^ı ⊑ s ] T
  deriving(Show)

type Type = Term

type IsStar = Bool

-- | Constrained types
data ConstrType
  = ConstrType [Name] Type -- ^ Top level type of the form
                           --   { i j k } -> T
                           --   where i j k are size variables

mkPi :: Context -> Term -> Term
mkPi ctx t | ctxIsNull ctx = t
           | otherwise = case t of
                           Pi ctx2 t' -> Pi (ctx <> ctx2) t'
                           _          -> Pi ctx t


unPi :: Term -> (Context, Term)
unPi (Pi c t) = (c <> c', t')
  where (c', t') = unPi t
unPi t = (ctxEmpty, t)


subsetType :: SizeName -> Annot -> Type -> Type
subsetType = Subset


mkApp :: Term -> [Term] -> Term
mkApp (App t as) as'    = App t (as ++ as')
mkApp t          []     = t
mkApp t          (a:as) = App t (a:as)


unApp :: Term -> (Term, [Term])
unApp (App t ts) = (func, args++ts)
  where (func, args) = unApp t
unApp t = (t, [])


mkLam :: Context -> Term -> Term
mkLam ctx t | ctxIsNull ctx = t
            | otherwise = case t of
                            Lam ctx2 t' -> Lam (ctx <> ctx2) t'
                            _           -> Lam ctx t


unLam :: Term -> (Context, Term)
unLam (Lam c t) = (c <> c', t')
  where (c', t') = unLam t
unLam t = (ctxEmpty, t)


-- | Meta variables

newtype MetaVar = MetaVar Int
                  deriving(Eq, Enum, Num, Ord)

instance Show MetaVar where
  show (MetaVar k) = '?' : show k


-- | Binds, contexts, and environments

data Bind
  = Bind { bindName :: Name
         , bindType :: Arg Type
         , bindDef  :: Maybe Term
         } deriving(Show)

type Context = Ctx Bind

type Environment = Env Bind


instance HasNames Bind where
  name x = [bindName x]


mkBind :: Name -> Type -> Bind
mkBind x t = Bind x (mkArg t) Nothing

mkBindDef :: Name -> Type -> Term -> Bind
mkBindDef x t e = Bind x (mkArg t) (Just e)


unNamed :: Type -> Bind
unNamed t = Bind noName (mkArg t) Nothing


renameBind :: Bind -> SinglePattern -> Bind
renameBind b (PatternVar x) = b { bindName = x}
renameBind b (PatternDef x t) = b { bindName = x
                                  , bindDef = Just t }

renameCtx :: Context -> Pattern -> Context
renameCtx CtxEmpty [] = CtxEmpty
renameCtx (b :> bs) (p:ps) = renameBind b p :> renameCtx bs ps


applyCtxDef :: Context -> Int -> Term -> Context
applyCtxDef ctx n t = ctxUpdate ctx n (\b -> b { bindDef = Just t})

revapplyCtxDef :: Context -> Int -> Term -> Context
revapplyCtxDef ctx n t = revCtxUpdate ctx n (\b -> b { bindDef = Just t})

boundArgs :: Int -> [Term]
boundArgs n = reverse (take n (map Bound [0..]))


-- | Pattern
data SinglePattern
  = PatternVar Name
  | PatternDef Name Term
  deriving(Show)

instance HasNames SinglePattern where
  name (PatternVar x)   = name x
  name (PatternDef x _) = name x

type Pattern = [SinglePattern]


isPatternDef :: SinglePattern -> Bool
isPatternDef (PatternDef _ _) = True
isPatternDef _ = False


-- | Case expressions

data CaseTerm
  = CaseTerm { caseKind     :: CaseKind Annot
             , caseArg      :: Term
             , caseNmInd    :: Name
             , caseAsName   :: Name
             , caseIndType  :: Name
             , caseIndPars  :: [Term]
             , caseIndices  :: Pattern
             , caseTpRet    :: Type
             , caseBranches :: [Branch]
             } deriving(Show)


data IndicesSpec
  = IndicesSpec { indspecArgs :: [Named (Maybe Term)]
                } deriving(Show)


data Branch
  = Branch { brSize     :: Maybe SizeName
           , brName     :: Name
           , brConstrId :: Int
           , brArgNames :: Pattern
           , brBody     :: Term
           } deriving(Show)


newtype Subst = Subst { unSubst :: [(Int, Term)] }

instance HasNames IndicesSpec where
  name = name . indspecArgs

instance Sized IndicesSpec where
  size = size . indspecArgs


isCocase :: CaseTerm -> Bool
isCocase c | CaseKind <- caseKind c = False
           | otherwise              = True

getCocaseSize :: CaseTerm -> Annot
getCocaseSize c | CocaseKind a <- caseKind c = a

-- | (Co-)fix expressions
data FixTerm
  = FixTerm { fixKind :: InductiveKind
            , fixNum  :: Int -- (-1) for CoI
            , fixName :: Name
            , fixSpec :: FixSpec
            , fixArgs :: Context
            , fixType :: Type
            , fixBody :: Term
            } deriving(Show)

data FixSpec
  = FixStruct
  | FixPosition
  | FixStage Name
  deriving(Show)

getFixStage :: FixTerm -> Name
getFixStage f | FixStage s <- fixSpec f = s


-- | Goals

data Goal
  = Goal { goalEnv  :: Environment
         , goalType :: Type
         , goalTerm :: Maybe Term
         }

mkGoal :: Environment -> Type -> Goal
mkGoal env tp = Goal env tp Nothing


-- | Global declarations

data Global
  = Definition { defType :: ConstrType
               , defTerm :: Term
               }
  | Assumption { assumeType :: ConstrType }
  | Inductive { indKind    :: InductiveKind
              , indPars    :: Context
              , indPol     :: [Polarity]
              , indIndices :: Context
              , indSort    :: Sort
              , indConstr  :: [Name]
              }
  | Constructor { constrInd     :: Name
                , constrId      :: Int
                  -- ^ id
                , constrPars    :: Context
                  -- ^ Parameters, should be the same as the indutive type
                , constrArgs    :: Context
                  -- ^ Arguments
                , constrRec     :: [Int]
                  -- ^ Indicates the positions of recursive arguments
                , constrIndices :: [Term]
                  -- ^ Indices in the return type
                }
  | Cofixpoint { cofixTerm :: FixTerm
               , cofixType :: ConstrType }



isConstr :: Global -> Bool
isConstr (Constructor {}) = True
isConstr _                = False

-- | Useful functions to work with inductive types

getIndParameters :: Global -> Context
getIndParameters = indPars


getIndIndices :: Global -> [Term] -> Context
getIndIndices i pars = substList0 pars (indIndices i)


getIndSort :: Global -> Sort
getIndSort = indSort


getIndType :: Global -> [Term] -> Type
getIndType _ _ = Sort Prop


getConstrContext :: Global -> [Term] -> Annot -> Context
getConstrContext c pars stage = replStage (substList0 pars (constrArgs c))
                                -- (foldr subst (constrArgs c) pars)
  where
    replStage = modifySize (\x -> if x == Star then stage else x)

substList0 :: (SubstTerm a) => [Term] -> a -> a
-- substList0 xs s = foldl (\a (k,t) -> substN k t a) s
--                   (zip (reverse [0..length xs-1]) xs)

substList0 xs s = foldl (flip (uncurry substN)) s
                  (zip (reverse [0..length xs-1]) xs)


getConstrIndices :: Global -> [Term] -> [Term] -> [Term]
getConstrIndices c pars args = substList0 (pars ++ args) (constrIndices c)
                               -- substList (length (pars ++ args)) (pars ++ args) (constrIndices c)


------------------------------------------------------------
-- * Operations on sizes
------------------------------------------------------------

toInftyBut :: HasAnnot a => [Name] -> a -> a
toInftyBut xs = modifySize f
  where
    f a@(SizeVar s _) | s `notElem` xs = Stage Infty
                      | otherwise         = a
    f (Stage (StageVar _ _)) = Stage Infty
    f s = s

toInfty :: HasAnnot a => a -> a
toInfty = toInftyBut []


class HasAnnot a where
  modifySize :: (Annot   -> Annot) -> a -> a
  eraseSize  :: a        -> a
  eraseStage :: StageVar -> a -> a
  fAnnot  :: a        -> Set Annot

  -- Compatibility
  listAnnot  :: a        -> [Annot]
  listAnnot = Set.elems . fAnnot

  substSize :: (StageVar -> Annot) -> a -> a
  substSize f = modifySize f'
    where
      f' s@Empty = s
      f' s@Star = s
      f' (Stage (StageVar x n)) = hatn n (f x)
      f' s@(Stage Infty) = s
      f' s@(SizeVar _ _) = s

--  getSizes :: a -> [Size]

  eraseSize    = modifySize $ const Empty
  eraseStage i = modifySize f
    where f Empty    = Empty
          -- f Star     = Star
          f s@(Stage Infty)    = s
          f s@(Stage (StageVar a _)) | a == i    = Empty
                             | otherwise = s
          -- f (Size s) = case base s of
          --                Just j | i == j    -> Empty -- Star
          --                       | otherwise -> Empty
          --                Nothing            -> Empty

substSizeName :: (HasAnnot a) => SizeName -> Annot -> a -> a
substSizeName i a = modifySize f
  where
    f (SizeVar j n) | i == j = hatn n a
    f s                      = s

substSizeNames :: (HasAnnot a) => [(SizeName, Annot)] -> a -> a
substSizeNames is = modifySize f
  where
    f (SizeVar j n) | Just a <- lookup j is = hatn n a
    f s                                     = s

substStageVars :: (HasAnnot a) => [(StageVar, Annot)] -> a -> a
substStageVars is = modifySize f
  where
    f (Stage (StageVar x n)) | Just a <- lookup x is = hatn n a
    f s                                              = s

instance HasAnnot Annot where
  modifySize f = f
  fAnnot x = maybe Set.empty Set.singleton (baseAnnot x)

instance (HasAnnot a) => HasAnnot (Maybe a) where
  modifySize = fmap . modifySize

  fAnnot = maybe Set.empty fAnnot

instance HasAnnot a => HasAnnot (Named a) where
  modifySize = fmap . modifySize
  fAnnot = fAnnot . namedValue

instance (HasAnnot a) => HasAnnot (Implicit a) where
  modifySize = fmap . modifySize

  fAnnot = fAnnot . implicitValue


instance HasAnnot a => HasAnnot [a] where
  modifySize = map . modifySize

  fAnnot = Set.unions . map fAnnot

instance HasAnnot Term where
  modifySize f = mSize
    where
      mSize t@(Sort _)           = t
      mSize (Pi c t)             = Pi (modifySize f c) (mSize t)
      mSize t@(Bound _)          = t
      mSize t@(Var _)            = t
      mSize (SIdent x a)         = SIdent x (f a)
      mSize (Lam c t)            = Lam (modifySize f c) (mSize t) -- Lam (modifySize f c) (mSize t)
      mSize (App t ts)           = App (mSize t) (map mSize ts)
      mSize t@(Meta _)           = t
      mSize (Constr nm cid pars) = Constr nm cid (map mSize pars)
      mSize (Fix c)              = Fix (modifySize f c)
      mSize (Case c)             = Case (modifySize f c)
      mSize (Ind a b x ps)       = Ind (f a) b x (map mSize ps)
      -- Well-founded sizes
      mSize (Intro s t)          = Intro (f s) (mSize t)
      mSize (CoIntro k a t)      = CoIntro k (f a) (mSize t)
      mSize (SizeApp t s)        = SizeApp (mSize t) (f s)
      mSize (Subset i a t)       = Subset i (f a) (mSize t)

  fAnnot (Sort _)          = Set.empty
  fAnnot (Pi c t)          = fAnnot c `Set.union` fAnnot t
  fAnnot (Bound _)         = Set.empty
  fAnnot (Var _)           = Set.empty
  fAnnot (Lam c t)         = {- fAnnot c `Set.union` -} fAnnot t
  fAnnot (App t ts)        = fAnnot t `Set.union` fAnnot ts
  fAnnot (Meta _)          = Set.empty
  fAnnot (Constr _ _ pars) = fAnnot pars
  fAnnot (Fix c)           = fAnnot c
  fAnnot (Case c)          = fAnnot c
  fAnnot (Ind a _ _ ts)    = fAnnot a `Set.union` fAnnot ts
  -- Well-founded sizes
  fAnnot (Intro a t)       = {- fAnnot a `Set.union` -} fAnnot t
  fAnnot (CoIntro k a t)   = Set.delete (mkAnnot k) (fAnnot t)
  fAnnot (SizeApp t s)     = fAnnot t -- `Set.union` fAnnot s
  fAnnot (Subset i a t)    = {- fAnnot a `Set.union` -}
                             (Set.delete (mkAnnot i) (fAnnot t))



instance HasAnnot ConstrType where
  modifySize f (ConstrType xs t) =  ConstrType xs (modifySize f t)
  fAnnot (ConstrType _ t) = fAnnot t


instance HasAnnot FixTerm where
  modifySize f (FixTerm k n x spec c t1 t2) =
    -- FixTerm k n x spec (modifySize f c) (modifySize f t1) (modifySize f t2)
    FixTerm k n x spec (modifySize f c) (modifySize f t1) (modifySize f t2)

  fAnnot (FixTerm _ _ _ (FixStage im) args tp body) =
    {- Set.delete (mkAnnot im) (fAnnot args `Set.union` fAnnot tp)
    `Set.union` -} fAnnot body
  -- fAnnot _ = __IMPOSSIBLE__

instance HasAnnot a => HasAnnot (CaseKind a) where
  modifySize _ CaseKind = CaseKind
  modifySize f (CocaseKind a) = CocaseKind (modifySize f a)

  fAnnot CaseKind = Set.empty
  fAnnot (CocaseKind a) = fAnnot a

instance HasAnnot CaseTerm where
  modifySize f (CaseTerm kind arg nm asName nmInd pars cin ret bs) =
    CaseTerm (modifySize f kind) (modifySize f arg) nm asName nmInd (modifySize f pars) (modifySize f cin) (modifySize f ret) (map (modifySize f) bs)

  fAnnot (CaseTerm kind arg _ _ _ pars cin _ bs) =
    -- fAnnot kind `Set.union`
    fAnnot arg `Set.union`
    fAnnot pars `Set.union`
    fAnnot cin `Set.union`
    fAnnot bs

instance HasAnnot SinglePattern where
  modifySize _ (PatternVar x)   = PatternVar x
  modifySize f (PatternDef x t) = PatternDef x (modifySize f t)

  fAnnot (PatternDef _ t) = fAnnot t
  fAnnot _                = Set.empty


instance HasAnnot IndicesSpec where
  modifySize f (IndicesSpec args) = IndicesSpec (map (modifySize f) args)

  fAnnot (IndicesSpec args) = fAnnot args

instance HasAnnot Branch where
  modifySize f (Branch sv nm cid nmArgs body) =
    Branch sv nm cid nmArgs (modifySize f body)

  fAnnot (Branch (Just sv) _ _ _ body) = Set.delete (mkAnnot sv) (fAnnot body)
  fAnnot (Branch Nothing _ _ _ body) = fAnnot body


instance HasAnnot Subst where
  modifySize f (Subst sg) = Subst $ map (appSnd (modifySize f)) sg

  fAnnot (Subst sg) = Set.unions $ map (fAnnot . snd) sg

instance HasAnnot a => HasAnnot (Arg a) where
  modifySize = fmap . modifySize
  fAnnot = fAnnot . unArg

instance HasAnnot Bind where
  modifySize f (Bind x t u) = Bind x (modifySize f t) (modifySize f u)

  fAnnot b = fAnnot (bindType b) `Set.union` fAnnot (bindDef b)

instance HasAnnot a => HasAnnot (Ctx a) where
  modifySize f = fmap (modifySize f)

  fAnnot = Fold.foldMap fAnnot

instance HasAnnot Global where
  modifySize f (Definition tp body) =
    Definition (modifySize f tp) (modifySize f body)
  modifySize f (Assumption tp) = Assumption (modifySize f tp)
  modifySize f (Inductive k pars pol indices sort constr) =
    Inductive k (modifySize f pars) pol (modifySize f indices) sort constr
  modifySize f (Constructor nmInd cid pars args ret indices) =
    Constructor nmInd cid (modifySize f pars) (modifySize f args) ret (modifySize f indices)
  modifySize k (Cofixpoint t1 t2) = Cofixpoint (modifySize k t1) (modifySize k t2)

  fAnnot (Definition tp body) = fAnnot tp `Set.union` fAnnot body
  fAnnot (Assumption tp) = fAnnot tp
  fAnnot (Inductive _ pars _ indices _ _) = fAnnot pars `Set.union` fAnnot indices
  fAnnot (Constructor _ _ pars args _ indices) =
    fAnnot pars `Set.union` fAnnot args `Set.union` fAnnot indices
  fAnnot (Cofixpoint t1 t2) = fAnnot t1 `Set.union` fAnnot t2



------------------------------------------------------------
-- * Operations on de Bruijn indices
------------------------------------------------------------

------------------------------------------------------------
-- ** Shift
------------------------------------------------------------


class Lift a where
  lift :: Int -> Int -> a -> a
  lift0 :: Int -> a -> a
  lift0 n = lift n 0

instance Lift Int where
  lift k n m = if m < n then m else m + k

instance (Lift a, Lift b) => Lift (a, b) where
  lift k n (x, y) = (lift k n x, lift k n y)

instance Lift a => Lift (Maybe a) where
  lift k n = fmap (lift k n)

instance Lift a => Lift (Named a) where
  lift k n = fmap (lift k n)

instance Lift a => Lift (Implicit a) where
  lift k n = fmap (lift k n)

instance Lift a => Lift [a] where
  lift k n = map (lift k n)

-- instance Lift [Term] where
--   lift k n = map (lift k n)

instance Lift Subst where
  lift k n (Subst sg) = Subst $ map (lift k n) sg

instance Lift a => Lift (Arg a) where
  lift k n = fmap (lift k n)

instance Lift Bind where
  lift k n (Bind x t u) = Bind x (lift k n t) (lift k n u)

instance Lift a => Lift (Ctx a) where
  lift _ _ CtxEmpty  = CtxEmpty
  lift k n (x :> xs) = lift k n x :> lift k (n+1) xs

instance Lift Term where
  lift _ _ t@(Sort _)          = t
  lift k n (Pi c t)            = Pi (lift k n c) (lift k (n + ctxLen c) t)
  lift k n t@(Bound m)         = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _)           = t
  lift k n (Lam c u)           = Lam (lift k n c) (lift k (n + ctxLen c) u)
  lift k n (App t1 t2)         = App (lift k n t1) $ map (lift k n) t2
  lift _ _ t@(Meta _)          = t
  lift k n (Ind a b x ps)      = Ind a b x (map (lift k n) ps)
  lift k n (Constr x indId ps) = Constr x indId ps'
    where ps' = map (lift k n) ps
  lift k n (Fix f)             = Fix (lift k n f)
  lift k n (Case c)            = Case (lift k n c)
  -- Well-founded sizes
  lift k n (Intro a t)         = Intro a (lift k n t)
  lift k n (CoIntro x a t)     = CoIntro x a (lift k n t)
  lift k n (SizeApp t a)       = SizeApp (lift k n t) a
  lift k n (Subset i a t)      = Subset i a (lift k n t)


instance Lift FixTerm where
  lift k n (FixTerm a m x stagenm c t e) =
    FixTerm a m x stagenm (lift k n c) (lift k (n + ctxLen c) t) (lift k (n + ctxLen c + 1) e)

instance Lift CaseTerm where
  lift k n (CaseTerm kind arg nm asName nmInd pars cin ret branches) =
    CaseTerm kind (lift k n arg) nm asName nmInd (lift k n pars) (lift k n cin) (lift k (n + len) ret) (map (lift k n) branches)
      where len = length (name asName ++ name cin)

instance Lift SinglePattern where
  lift k n (PatternDef x t) = PatternDef x (lift k n t)
  lift _ _ t = t

instance Lift IndicesSpec where
  lift k n (IndicesSpec args) = IndicesSpec (map (lift k n) args)

instance Lift Branch where
  lift k n (Branch sv nm cid nmArgs body) =
    Branch sv nm cid nmArgs (lift k (n + length nmArgs) body)


------------------------------------------------------------
-- ** Substitution
------------------------------------------------------------


class SubstTerm a where
  subst :: Term -> a -> a
  substN :: Int -> Term -> a -> a

  subst = substN 0

-- |
substList :: (SubstTerm a) => Int -> [Term] -> a -> a
substList k xs t = foldl (flip (uncurry substN)) t (zip ks xs)
                   where ks = reverse [k - length xs + 1..k]

instance (SubstTerm a) => SubstTerm (Implicit a) where
  substN k = fmap . substN k

instance (SubstTerm a) => SubstTerm (Maybe a) where
  substN k = fmap . substN k

instance SubstTerm a => SubstTerm [a] where
  substN n r = map (substN n r)

instance SubstTerm a => SubstTerm (Arg a) where
  substN k = fmap . substN k

instance SubstTerm a => SubstTerm (Named a) where
  substN k = fmap . substN k

instance SubstTerm Bind where
  substN n r (Bind x t u) = Bind x (substN n r t) (substN n r u)

instance SubstTerm a => SubstTerm (Ctx a) where
  substN _ _ CtxEmpty = CtxEmpty
  substN n r (x :> xs) = substN n r x :> substN (n+1) r xs

instance SubstTerm Term where
  substN _ _ t@(Sort _) = t
  substN i r (Pi c t) = Pi (substN i r c) (substN (i + ctxLen c) r t)
  substN i r t@(Bound n) | n < i = t
                         | n == i = lift i 0 r
                         | otherwise = Bound (n - 1)
  substN _ _ t@(Var _) = t
  substN i r (Lam c t) = Lam (substN i (eraseSize r) c) (substN (i + ctxLen c) r t)
  substN i r (App t ts) = App (substN i r t) (map (substN i r) ts)
  substN _ _ t@(Meta _) = t
  substN i r (Ind a b x ps) = Ind a b x (map (substN i r) ps)
  substN i r (Constr x ind ps) = Constr x ind ps'
    where ps' = map (substN i (eraseSize r)) ps
  substN i r (Case c) = Case (substN i r c)
  substN i r (Fix f) = Fix (substN i r f)
  -- Well-founded sizes
  substN i r (Intro a t) = Intro a (substN i r t)
  substN i r (CoIntro x k t) = CoIntro x k (substN i r t)
  substN i r (SizeApp t s) = SizeApp (substN i r t) s
  substN i r (Subset x s t) = Subset x s (substN i r t)

instance SubstTerm FixTerm where
  substN i r (FixTerm a k nm stagenm c tp body) =
    FixTerm a k nm stagenm (substN i (eraseSize r) c) (substN (i + ctxLen c) (eraseSize r) tp) (substN (i + ctxLen c+1) r body)


instance SubstTerm CaseTerm where
  substN i r (CaseTerm kind arg nm cas nmInd pars cin ret branches) =
    CaseTerm kind (substN i r arg) nm cas nmInd (substN i r pars) (substN i r cin) (substN (i + len) (eraseSize r) ret) branches'
      where
        branches' = map (substN i r) branches
        len = length (name cas ++ name cin)

instance SubstTerm SinglePattern where
  substN i r (PatternDef x t) = PatternDef x (substN i r t)
  substN _ _ t = t

instance SubstTerm IndicesSpec where
  substN i r (IndicesSpec args) = IndicesSpec (map (substN i r) args)

instance SubstTerm Branch where
  substN i r (Branch sv nm cid xs body) =
    Branch sv nm cid xs (substN (i + length xs) r body)

instance SubstTerm Subst where
  substN i r (Subst sg) = Subst $ map (appSnd (substN i r)) sg



------------------------------------------------------------
-- ** Free bound variables
------------------------------------------------------------

type FreeBVars = [Int]

shiftFV :: Int -> FreeBVars -> FreeBVars
shiftFV k = filter (>0) . map (subtract k)

class IsFree a where
  isFree :: Int -> a -> Bool
  fvN :: Int -> a -> [Int]
  fv :: a -> [Int]

  fv = fvN 0

instance IsFree a => IsFree (Maybe a) where
  isFree _ Nothing = False
  isFree k (Just c) = isFree k c

  fvN = maybe [] . fvN

instance IsFree a => IsFree (Named a) where
  isFree k = isFree k . namedValue
  fvN k = fvN k . namedValue

instance IsFree a => IsFree (Implicit a) where
  isFree k = isFree k . implicitValue

  fvN k = fvN k . implicitValue

instance IsFree a => IsFree [a] where
  isFree k = any (isFree k)

  fvN k = concatMap (fvN k)

instance IsFree Term where
  isFree _ (Sort _) = False
  isFree k (Pi c t) = isFree k c || isFree (k + ctxLen c) t
  isFree k (Bound n) = k == n
  isFree _ (Var _) = False
  isFree k (Lam c t) = isFree k c || isFree (k + ctxLen c) t
  isFree k (App f ts) = isFree k f || any (isFree k) ts
  isFree _ (Meta _) = False
  isFree k (Ind _ _ _ ps) = any (isFree k) ps
  isFree k (Constr _ _ ps) = any (isFree k) ps
  isFree k (Fix f) = isFree k f
  isFree k (Case c) = isFree k c
  -- Well-founded sizes
  isFree k (Intro _ t) = isFree k t
  isFree k (CoIntro _ _ t) = isFree k t
  isFree k (SizeApp t _) = isFree k t
  isFree k (Subset _ _ t) = isFree k t

  fvN _ (Sort _) = []
  fvN k (Pi c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (Bound n) = if n < k then [] else [n]
  fvN _ (Var _) = []
  fvN k (Lam c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (App f ts) = fvN k f ++ concatMap (fvN k) ts
  fvN _ (Meta _) = []
  fvN k (Ind _ _ _ ps) = concatMap (fvN k) ps
  fvN k (Constr _ _ ps) = concatMap (fvN k) ps
  fvN k (Fix f) = fvN k f
  -- Well-founded sizes
  fvN k (Intro _ t) = fvN k t
  fvN k (CoIntro _ _ t) = fvN k t
  fvN k (SizeApp t _) = fvN k t
  fvN k (Subset _ _ t) = fvN k t

instance IsFree FixTerm where
  isFree k (FixTerm _ _ _ _ bs tp body) = isFree k (mkPi bs tp) || isFree (k+1) body

  fvN k (FixTerm _ _ _ _ bs tp body) = fvN k (mkPi bs tp) ++ fvN (k + 1) body


instance IsFree CaseTerm where
  isFree k (CaseTerm _ arg _ _ _ pars cin tpRet branches) =
    isFree k arg || isFree k pars || isFree (k + size cin + 1) tpRet || isFree k cin || any (isFree k) branches

  fvN k (CaseTerm _ arg _ _ _ pars cin tpRet branches) =
    fvN k arg ++ fvN k pars ++ fvN (k + size cin + 1) tpRet ++ fvN k cin ++ concatMap (fvN k) branches

instance IsFree SinglePattern where
  isFree k (PatternDef _ t) = isFree k t
  isFree _ _ = False

  fvN k (PatternDef _ t) = fvN k t
  fvN _ _ = []

instance IsFree IndicesSpec where
  isFree k (IndicesSpec args) = any (isFree k) args

  fvN k (IndicesSpec args) = fvN k args

instance IsFree Branch where
  isFree k (Branch _ _ _ nmArgs body) =
    isFree (k + length nmArgs) body

  fvN k (Branch _ _ _ nmArgs body) = fvN k1 body
    where
      k1 = k + length nmArgs

instance IsFree Subst where
  isFree k (Subst sg) = any (isFree k . snd) sg

  fvN k (Subst sg) = concatMap (fvN k . snd) sg

instance IsFree a => IsFree (Arg a) where
  isFree k = isFree k . unArg
  fvN k = fvN k . unArg

instance IsFree Bind where
  isFree k b = isFree k (bindType b) || isFree k (bindDef b)

  fvN k b = fvN k (bindType b) ++ fvN k (bindDef b)

instance IsFree a => IsFree (Ctx a) where
  isFree _ CtxEmpty = False
  isFree k (x :> xs) = isFree k x || isFree (k+1) xs

  fvN _ CtxEmpty = []
  fvN k (x :> xs) = fvN k x ++ fvN (k+1) xs
