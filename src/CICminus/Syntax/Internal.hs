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

-- | Internal representation of Terms

module CICminus.Syntax.Internal where

import qualified Data.Foldable as Fold
import           Data.Monoid

import           CICminus.Syntax.Common

import           CICminus.Utils.Misc
import           CICminus.Utils.Sized


------------------------------------------------------------
-- * Size annotations for (co-)inductive types
------------------------------------------------------------

-- data Annot
--   = Empty             -- ^ No annotation (for bare terms);
--   | SBound Int        -- ^ For position types (in definition of (co-)fixpoints;
--   | Size Size         -- ^ An actual size annotation.

-- | Meta variables

newtype StageVar = SVar Int
                   deriving(Eq, Enum, Num, Ord)

instance Show StageVar where
  show (SVar k) = 'α' : show k


data Stage
  = StageVar StageVar Int
  | Infty
  deriving(Eq, Show)

data Annot
  = Empty
  | Star
  | Stage Stage
  | SizeVar Name Int
  deriving(Eq, Show)
  -- | StageVar StageVar Int
  -- | SBound Int

mkAnnot :: StageVar -> Annot
mkAnnot s = Stage (StageVar s 0)

infty :: Annot
infty = Stage Infty

hat :: Annot -> Annot
hat (Stage (StageVar s n)) = Stage (StageVar s (n+1))
hat (SizeVar s n) = SizeVar s (n+1)
hat s = s

sbase :: Annot -> Maybe StageVar
sbase (Stage (StageVar s _)) = Just s
sbase _ = Nothing

nbase :: Annot -> Maybe Name
nbase (SizeVar x _) = Just x
nbase _ = Nothing

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
  | Ind Annot Name [Term]  -- Inductive types are applied to parameters
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
  = CaseTerm { caseArg      :: Term
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
  = Branch { brName     :: Name
           , brConstrId :: Int
           , brArgNames :: Pattern
           , brBody     :: Term
           } deriving(Show)


newtype Subst = Subst { unSubst :: [(Int, Term)] }

instance HasNames IndicesSpec where
  name = name . indspecArgs

instance Sized IndicesSpec where
  size = size . indspecArgs


-- | (Co-)fix expressions
data FixTerm
  = FixTerm { fixKind      :: InductiveKind
            , fixNum       :: Int -- (-1) for CoI
            , fixName      :: Name
            , fixSpec      :: FixSpec
            , fixArgs      :: Context
            , fixType      :: Type
            , fixBody      :: Term
            } deriving(Show)

data FixSpec
  = FixStruct
  | FixPosition
  | FixStage Name
  deriving(Show)

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
  listAnnot  :: a        -> [Annot]

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

instance (HasAnnot a) => HasAnnot (Maybe a) where
  modifySize = fmap . modifySize

  listAnnot = maybe [] listAnnot

instance HasAnnot a => HasAnnot (Named a) where
  modifySize = fmap . modifySize
  listAnnot = listAnnot . namedValue

instance (HasAnnot a) => HasAnnot (Implicit a) where
  modifySize = fmap . modifySize

  listAnnot = listAnnot . implicitValue


instance HasAnnot a => HasAnnot [a] where
  modifySize = map . modifySize

  listAnnot = concatMap listAnnot

instance HasAnnot Term where
  modifySize f = mSize
    where
      mSize t@(Sort _)           = t
      mSize (Pi c t)             = Pi (modifySize f c) (mSize t)
      mSize t@(Bound _)          = t
      mSize t@(Var _)            = t
      mSize (Lam c t)            = Lam c (mSize t) -- Lam (modifySize f c) (mSize t)
      mSize (App t ts)           = App (mSize t) (map mSize ts)
      mSize t@(Meta _)           = t
      mSize (Constr nm cid pars) = Constr nm cid (map mSize pars)
      mSize (Fix c)              = Fix (modifySize f c)
      mSize (Case c)             = Case (modifySize f c)
      mSize (Ind a x ps)         = Ind (f a) x (map (modifySize f) ps)

  listAnnot (Sort _)          = []
  listAnnot (Pi c t)          = listAnnot c ++ listAnnot t
  listAnnot (Bound _)         = []
  listAnnot (Var _)           = []
  listAnnot (Lam c t)         = listAnnot c ++ listAnnot t
  listAnnot (App t ts)        = listAnnot t ++ listAnnot ts
  listAnnot (Meta _)          = []
  listAnnot (Constr _ _ pars) = listAnnot pars
  listAnnot (Fix c)           = listAnnot c
  listAnnot (Case c)          = listAnnot c
  listAnnot (Ind a _ _)       = [a]

instance HasAnnot ConstrType where
  modifySize f (ConstrType xs t) =  ConstrType xs (modifySize f t)
  listAnnot (ConstrType _ t) = listAnnot t


instance HasAnnot FixTerm where
  modifySize f (FixTerm k n x spec c t1 t2) =
    -- FixTerm k n x spec (modifySize f c) (modifySize f t1) (modifySize f t2)
    FixTerm k n x spec c t1 (modifySize f t2)

  listAnnot (FixTerm _ _ _ _ _ _ t2) = listAnnot t2
    -- filter f (listAnnot c ++ listAnnot t1) ++ listAnnot t2
    -- where
    --   f (SizeVar x _) = x == sta
    --   f _ = True

instance HasAnnot CaseTerm where
  modifySize f (CaseTerm arg nm asName nmInd pars cin ret bs) =
    CaseTerm (modifySize f arg) nm asName nmInd (modifySize f pars) (modifySize f cin) ret (map (modifySize f) bs)

  listAnnot (CaseTerm arg _ _ _ pars cin _ bs) = listAnnot arg ++
                                                 listAnnot pars ++
                                                 listAnnot cin ++
                                                 -- listAnnot ret ++
                                                 listAnnot bs

instance HasAnnot SinglePattern where
  modifySize _ (PatternVar x)   = PatternVar x
  modifySize f (PatternDef x t) = PatternDef x (modifySize f t)

  listAnnot (PatternDef _ t) = listAnnot t
  listAnnot _                = []


instance HasAnnot IndicesSpec where
  modifySize f (IndicesSpec args) = IndicesSpec (map (modifySize f) args)

  listAnnot (IndicesSpec args) = listAnnot args

instance HasAnnot Branch where
  modifySize f (Branch nm cid nmArgs body) =
    Branch nm cid nmArgs (modifySize f body)

  listAnnot (Branch _ _ _ body) = listAnnot body


instance HasAnnot Subst where
  modifySize f (Subst sg) = Subst $ map (appSnd (modifySize f)) sg

  listAnnot (Subst sg) = concatMap (listAnnot . snd) sg

instance HasAnnot a => HasAnnot (Arg a) where
  modifySize = fmap . modifySize
  listAnnot = listAnnot . unArg

instance HasAnnot Bind where
  modifySize f (Bind x t u) = Bind x (modifySize f t) (modifySize f u)

  listAnnot b = listAnnot (bindType b) ++ listAnnot (bindDef b)

instance HasAnnot a => HasAnnot (Ctx a) where
  modifySize f = fmap (modifySize f)

  listAnnot = Fold.foldr (\x r -> listAnnot x ++ r) []

instance HasAnnot Global where
  modifySize f (Definition tp body) =
    Definition (modifySize f tp) (modifySize f body)
  modifySize f (Assumption tp) = Assumption (modifySize f tp)
  modifySize f (Inductive k pars pol indices sort constr) =
    Inductive k (modifySize f pars) pol (modifySize f indices) sort constr
  modifySize f (Constructor nmInd cid pars args ret indices) =
    Constructor nmInd cid (modifySize f pars) (modifySize f args) ret (modifySize f indices)
  modifySize k (Cofixpoint t1 t2) = Cofixpoint (modifySize k t1) (modifySize k t2)

  listAnnot (Definition tp body) = listAnnot tp ++ listAnnot body
  listAnnot (Assumption tp) = listAnnot tp
  listAnnot (Inductive _ pars _ indices _ _) = listAnnot pars ++ listAnnot indices
  listAnnot (Constructor _ _ pars args _ indices) =
    listAnnot pars ++ listAnnot args ++ listAnnot indices
  listAnnot (Cofixpoint t1 t2) = listAnnot t1 ++ listAnnot t2



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
  lift k n (Ind a x ps)        = Ind a x (map (lift k n) ps)
  lift k n (Constr x indId ps) = Constr x indId ps'
    where ps' = map (lift k n) ps
  lift k n (Fix f)             = Fix (lift k n f)
  lift k n (Case c)            = Case (lift k n c)

instance Lift FixTerm where
  lift k n (FixTerm a m x stagenm c t e) =
    FixTerm a m x stagenm (lift k n c) (lift k (n + ctxLen c) t) (lift k (n + ctxLen c + 1) e)

instance Lift CaseTerm where
  lift k n (CaseTerm arg nm asName nmInd pars cin ret branches) =
    CaseTerm (lift k n arg) nm asName nmInd (lift k n pars) (lift k n cin) (lift k (n + len) ret) (map (lift k n) branches)
      where len = length (name asName ++ name cin)

instance Lift SinglePattern where
  lift k n (PatternDef x t) = PatternDef x (lift k n t)
  lift _ _ t = t

instance Lift IndicesSpec where
  lift k n (IndicesSpec args) = IndicesSpec (map (lift k n) args)

instance Lift Branch where
  lift k n (Branch nm cid nmArgs body) =
    Branch nm cid nmArgs (lift k (n + length nmArgs) body)


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
  substN i r (Ind a x ps) = Ind a x (map (substN i r) ps)
  substN i r (Constr x ind ps) = Constr x ind ps'
    where ps' = map (substN i (eraseSize r)) ps
  substN i r (Case c) = Case (substN i r c)
  substN i r (Fix f) = Fix (substN i r f)

instance SubstTerm FixTerm where
  substN i r (FixTerm a k nm stagenm c tp body) =
    FixTerm a k nm stagenm (substN i (eraseSize r) c) (substN (i + ctxLen c) (eraseSize r) tp) (substN (i + ctxLen c+1) r body)


instance SubstTerm CaseTerm where
  substN i r (CaseTerm arg nm cas nmInd pars cin ret branches) =
    CaseTerm (substN i r arg) nm cas nmInd (substN i r pars) (substN i r cin) (substN (i + len) (eraseSize r) ret) branches'
      where
        branches' = map (substN i r) branches
        len = length (name cas ++ name cin)

instance SubstTerm SinglePattern where
  substN i r (PatternDef x t) = PatternDef x (substN i r t)
  substN _ _ t = t

instance SubstTerm IndicesSpec where
  substN i r (IndicesSpec args) = IndicesSpec (map (substN i r) args)

instance SubstTerm Branch where
  substN i r (Branch nm cid xs body) =
    Branch nm cid xs (substN (i + length xs) r body)

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
  isFree k (Ind _ _ ps) = any (isFree k) ps
  isFree k (Constr _ _ ps) = any (isFree k) ps
  isFree k (Fix f) = isFree k f
  isFree k (Case c) = isFree k c

  fvN _ (Sort _) = []
  fvN k (Pi c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (Bound n) = if n < k then [] else [n]
  fvN _ (Var _) = []
  fvN k (Lam c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (App f ts) = fvN k f ++ concatMap (fvN k) ts
  fvN _ (Meta _) = []
  fvN k (Ind _ _ ps) = concatMap (fvN k) ps
  fvN k (Constr _ _ ps) = concatMap (fvN k) ps
  fvN k (Fix f) = fvN k f

instance IsFree FixTerm where
  isFree k (FixTerm _ _ _ _ bs tp body) = isFree k (mkPi bs tp) || isFree (k+1) body

  fvN k (FixTerm _ _ _ _ bs tp body) = fvN k (mkPi bs tp) ++ fvN (k + 1) body


instance IsFree CaseTerm where
  isFree k (CaseTerm arg _ _ _ pars cin tpRet branches) =
    isFree k arg || isFree k pars || isFree k tpRet || isFree k cin || any (isFree k) branches

  fvN k (CaseTerm arg _ _ _ pars cin tpRet branches) =
    fvN k arg ++ fvN k pars ++ fvN k tpRet ++ fvN k cin ++ concatMap (fvN k) branches

instance IsFree SinglePattern where
  isFree k (PatternDef _ t) = isFree k t
  isFree _ _ = False

  fvN k (PatternDef _ t) = fvN k t
  fvN _ _ = []

instance IsFree IndicesSpec where
  isFree k (IndicesSpec args) = any (isFree k) args

  fvN k (IndicesSpec args) = fvN k args

instance IsFree Branch where
  isFree k (Branch _ _ nmArgs body) =
    isFree (k + length nmArgs) body

  fvN k (Branch _ _ nmArgs body) = fvN k1 body
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
