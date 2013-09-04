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

{-# LANGUAGE CPP, FlexibleInstances, StandaloneDeriving, GeneralizedNewtypeDeriving
  #-}

-- | Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"

import qualified Data.Foldable as Fold
import Data.Monoid

import qualified Text.PrettyPrint as PP

import Syntax.Common
import Syntax.Size

import Utils.Misc
import Utils.Sized
import Utils.Pretty


data Term
    = Sort Sort
    | Pi Context Term
    | Bound Int
    | Var Name
    | Lam Context Term
    | App Term [Term]
    | Meta MetaVar
    | Constr Name (Name, Int) [Term] -- Constructors are applied to parameters
    | Fix FixTerm
    | Case CaseTerm
    | Ind Annot Name [Term]  -- Inductive types are applied to parameters

type Type = Term


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
  show (MetaVar k) = show k

instance Pretty MetaVar where
  prettyPrint (MetaVar k) = PP.text "?" PP.<> PP.int k


-- | Universes

data Sort = Prop
          | Type Int
          deriving(Show, Eq)


-- | Binds, contexts, and environments

data Bind =
  Bind { bindName :: Name
       , bindImplicit :: Bool
       , bindType :: Type
       , bindDef :: (Maybe Term)
       }

type Context = Ctx Bind

type Environment = Env Bind


instance HasImplicit Bind where
  isImplicit = bindImplicit
  modifyImplicit f (Bind x b t u) = Bind x (f b) t u

instance HasNames Bind where
  name x = [bindName x]


mkBind :: Name -> Type -> Bind
mkBind x t = Bind x False t Nothing


mkImplBind :: Name -> Bool -> Type -> Bind
mkImplBind x b t = Bind x b t Nothing


unNamed :: Type -> Bind
unNamed t = Bind noName False t Nothing


renameCtx :: Context -> [Name] -> Context
renameCtx CtxEmpty [] = CtxEmpty
renameCtx (b :> bs) (x:xs) = b { bindName = x} :> renameCtx bs xs


-- | Case expressions

data CaseTerm =
  CaseTerm { caseArg :: Term
           , caseNmInd :: Name
           , caseAsName :: Maybe Name
           , caseIn :: Maybe CaseIn
           , caseTpRet :: Type
           , caseBranches :: [Branch]
           } --deriving(Eq)


data CaseIn =
  CaseIn { inBind :: Context
         , inInd :: Name
         , inArgs :: [Term]
         } --deriving(Eq)


data Branch =
  Branch { brName :: Name
         , brConstrId :: Int
         , brArgNames :: [Name]
         , brBody :: Term
         , brSubst :: Maybe Subst
         } --deriving(Eq)


newtype Subst = Subst { unSubst :: [(Int, Term)] }

instance HasNames CaseIn where
  name = name . inBind

instance Sized CaseIn where
  size = size . inBind


-- | (Co-)fix expressions
data FixTerm =
  FixTerm { fixKind :: InductiveKind
          , fixNum :: Int
          , fixName :: Name
          , fixArgs :: Context
          , fixType :: Type
          , fixBody :: Term
          }


-- | Goals

data Goal = Goal { goalEnv  :: Environment
                 , goalType :: Type
                 , goalTerm :: Maybe Term
                 }

mkGoal :: Environment -> Type -> Goal
mkGoal env tp = Goal env tp Nothing


-- | Global declarations

data Global
  = Definition { defType :: Type
               , defTerm :: Term
               }
  | Assumption { assumeType :: Type }
  | Inductive { indKind :: InductiveKind
              , indPars :: Context
              , indPol :: [Polarity]
              , indIndices :: Context
              , indSort :: Sort
              , indConstr :: [Name]
              }
  | Constructor { constrInd :: Name
                , constrId :: Int
                  -- ^ id
                , constrPars :: Context
                  -- ^ Parameters, should be the same as the indutive type
                , constrArgs :: Context
                  -- ^ Arguments
                , constrRec :: [Int]
                  -- ^ Indicates the positions of recursive arguments
                , constrIndices :: [Term]
                  -- ^ Indices in the return type
                }

isConstr :: Global -> Bool
isConstr (Constructor {}) = True
isConstr _                = False


------------------------------------------------------------
-- * Operations on sizes
------------------------------------------------------------

class HasAnnot a where
  modifySize :: (Annot -> Annot) -> a -> a
  eraseSize :: a -> a
  eraseStage :: StageVar -> a -> a
  listAnnot :: a -> [StageVar]

--  getSizes :: a -> [Size]

  eraseSize = modifySize $ const Empty
  eraseStage i = modifySize f
    where f Empty    = Empty
          f Star     = Star
          f (Size s) = case base s of
                         Just j | i == j    -> Star
                                | otherwise -> Empty
                         Nothing            -> Empty

instance (HasAnnot a) => HasAnnot (Maybe a) where
  modifySize = fmap . modifySize

  listAnnot = maybe [] listAnnot

instance (HasAnnot a) => HasAnnot (Implicit a) where
  modifySize = fmap . modifySize

  listAnnot = listAnnot . implicitValue


instance HasAnnot a => HasAnnot [a] where
  modifySize f = map (modifySize f)

  listAnnot = concatMap listAnnot

instance HasAnnot Term where
  modifySize f = mSize
    where
      mSize t@(Sort _) = t
      mSize (Pi c t) = Pi (modifySize f c) (mSize t)
      mSize t@(Bound _) = t
      mSize t@(Var _) = t
      mSize (Lam c t) = Lam (modifySize f c) (mSize t)
      mSize (App t ts) = App (mSize t) (map mSize ts)
      mSize t@(Meta _) = t
      mSize (Constr nm cid pars) = Constr nm cid (map mSize pars)
      mSize (Fix c) = Fix (modifySize f c)
      mSize (Case c) = Case (modifySize f c)
      mSize (Ind a x ps) = Ind (f a) x (map (modifySize f) ps)

  listAnnot t@(Sort _) = []
  listAnnot (Pi c t) = listAnnot c ++ listAnnot t
  listAnnot t@(Bound _) = []
  listAnnot t@(Var _) = []
  listAnnot (Lam c t) = listAnnot c ++ listAnnot t
  listAnnot (App t ts) = listAnnot t ++ listAnnot ts
  listAnnot t@(Meta _) = []
  listAnnot (Constr _ _ pars) = listAnnot pars
  listAnnot (Fix c) = listAnnot c
  listAnnot (Case c) = listAnnot c
  listAnnot (Ind a x _) = case a of
                          (Size (Svar i)) -> [i]
                          _ -> []

instance HasAnnot FixTerm where
  modifySize f (FixTerm k n x c t1 t2) =
    FixTerm k n x (modifySize f c) (modifySize f t1) (modifySize f t2)

  listAnnot (FixTerm _ _ _ c t1 t2) = listAnnot c ++ listAnnot t1 ++ listAnnot t2

instance HasAnnot CaseTerm where
  modifySize f (CaseTerm arg nm asName cin ret bs) =
    CaseTerm (modifySize f arg) nm asName (modifySize f cin) (modifySize f ret) (map (modifySize f) bs)

  listAnnot (CaseTerm arg _ _ cin ret bs) = listAnnot arg ++
                                            listAnnot cin ++
                                            listAnnot ret ++
                                            listAnnot bs

instance HasAnnot CaseIn where
  modifySize f (CaseIn binds nmInd args) = CaseIn (modifySize f binds) nmInd (map (modifySize f) args)

  listAnnot (CaseIn binds _ args) = listAnnot binds ++ listAnnot args

instance HasAnnot Branch where
  modifySize f (Branch nm cid nmArgs body whSubst) =
    Branch nm cid nmArgs (modifySize f body) (modifySize f whSubst)

  listAnnot (Branch _ _ _ body whSubst) = listAnnot body ++ listAnnot whSubst


instance HasAnnot Subst where
  modifySize f (Subst sg) = Subst $ map (appSnd (modifySize f)) sg

  listAnnot (Subst sg) = concatMap (listAnnot . snd) sg

instance HasAnnot Bind where
  modifySize f (Bind x b t u) = Bind x b (modifySize f t) (modifySize f u)

  listAnnot b = listAnnot (bindType b) ++ listAnnot (bindDef b)

instance HasAnnot a => HasAnnot (Ctx a) where
  modifySize f c = fmap (modifySize f) c

  listAnnot = Fold.foldr (\x r -> listAnnot x ++ r) []

instance HasAnnot Global where
  modifySize f (Definition tp body) =
    Definition (modifySize f tp) (modifySize f body)
  modifySize f (Assumption tp) = Assumption (modifySize f tp)
  modifySize f (Inductive k pars pol indices sort constr) =
    Inductive k (modifySize f pars) pol (modifySize f indices) sort constr
  modifySize f (Constructor nmInd cid pars args rec indices) =
    Constructor nmInd cid (modifySize f pars) (modifySize f args) rec (modifySize f indices)

  listAnnot (Definition tp body) = listAnnot tp ++ listAnnot body
  listAnnot (Assumption tp) = listAnnot tp
  listAnnot (Inductive _ pars _ indices _ _) = listAnnot pars ++ listAnnot indices
  listAnnot (Constructor _ _ pars args _ indices) =
    listAnnot pars ++ listAnnot args ++ listAnnot indices



------------------------------------------------------------
-- * Operations on de Bruijn indices
------------------------------------------------------------

------------------------------------------------------------
-- ** Shift
------------------------------------------------------------


class Lift a where
  lift :: Int -> Int -> a -> a

instance Lift Int where
  lift k n m = if m < n then m else (m + k)

instance (Lift a, Lift b) => Lift (a, b) where
  lift k n (x, y) = (lift k n x, lift k n y)

instance Lift a => Lift (Maybe a) where
  lift k n = fmap (lift k n)

instance Lift a => Lift (Implicit a) where
  lift k n = fmap (lift k n)

-- instance Lift a => Lift [a] where
--   lift k n = map (lift k n)

instance Lift Subst where
  lift k n (Subst sg) = Subst $ map (lift k n) sg

instance Lift Bind where
  lift k n (Bind x b t u) = Bind x b (lift k n t) (lift k n u)

instance Lift a => Lift (Ctx a) where
  lift k n CtxEmpty = CtxEmpty
  lift k n (x :> xs) = lift k n x :> lift k (n+1) xs

instance Lift Term where
  lift _ _ t@(Sort _) = t
  lift k n (Pi c t) = Pi (lift k n c) (lift k (n + ctxLen c) t)
  lift k n t@(Bound m) = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _) = t
  lift k n (Lam c u) = Lam (lift k n c) (lift k (n + ctxLen c) u)
  lift k n (App t1 t2) = App (lift k n t1) $ map (lift k n) t2
  lift k n t@(Meta _) = t
  lift k n (Ind a x ps) = Ind a x (map (lift k n) ps)
  lift k n (Constr x indId ps) = Constr x indId ps'
    where ps' = map (lift k n) ps
  lift k n (Fix f) = Fix (lift k n f)
  lift k n (Case c) = Case (lift k n c)

instance Lift FixTerm where
  lift k n (FixTerm a m x c t e) =
    FixTerm a m x (lift k n c) (lift k (n + ctxLen c) t) (lift k (n + 1) e)

instance Lift CaseTerm where
  lift k n (CaseTerm arg nm asName cin ret branches) =
    CaseTerm (lift k n arg) nm asName (lift k n cin) (lift k (n + len) ret) (map (lift k n) branches)
      where len = length (name asName ++ name cin)

instance Lift CaseIn where
  lift k n (CaseIn binds nmInd args) = CaseIn (lift k n binds) nmInd (map (lift k (n + ctxLen binds)) args)

instance Lift Branch where
  lift k n (Branch nm cid nmArgs body whSubst) =
    Branch nm cid nmArgs (lift k (n + length nmArgs) body) (lift k (n + length nmArgs) whSubst)


------------------------------------------------------------
-- ** Substitution
------------------------------------------------------------


class SubstTerm a where
  subst :: Term -> a -> a
  substN :: Int -> Term -> a -> a

  subst = substN 0


substList :: (SubstTerm a) => Int -> [Term] -> a -> a
substList k xs t = foldl (flip (uncurry substN)) t (zip ks xs)
                   where ks = reverse [k - (length xs) + 1..k]

instance (SubstTerm a) => SubstTerm (Implicit a) where
  substN k = fmap . substN k

instance (SubstTerm a) => SubstTerm (Maybe a) where
  substN k = fmap . substN k

instance SubstTerm a => SubstTerm [a] where
  substN n r = map (substN n r)

instance SubstTerm Bind where
  substN n r (Bind x b t u) = Bind x b (substN n r t) (substN n r u)

instance SubstTerm a => SubstTerm (Ctx a) where
  substN n r CtxEmpty = CtxEmpty
  substN n r (x :> xs) = substN n r x :> substN (n+1) r xs

instance SubstTerm Term where
  substN _ _ t@(Sort _) = t
  substN i r (Pi c t) = Pi (substN i r c) (substN (i + ctxLen c) r t)
  substN i r t@(Bound n) | n < i = t
                         | n == i = lift i 0 r
                         | otherwise = Bound (n - 1)
  substN _ _ t@(Var _) = t
  substN i r (Lam c t) = Lam (substN i r c) (substN (i + ctxLen c) r t)
  substN i r (App t ts) = App (substN i r t) (map (substN i r) ts)
  substN i r t@(Meta _) = t
  substN i r (Ind a x ps) = Ind a x (map (substN i r) ps)
  substN i r (Constr x ind ps) = Constr x ind ps'
    where ps' = map (substN i r) ps
  substN i r (Case c) = Case (substN i r c)
  substN i r (Fix f) = Fix (substN i r f)

instance SubstTerm FixTerm where
  substN i r (FixTerm a k nm c tp body) =
    FixTerm a k nm (substN i r c) (substN (i + ctxLen c) r tp) (substN (i + 1) r body)


instance SubstTerm CaseTerm where
  substN i r (CaseTerm arg nm cas cin ret branches) =
    CaseTerm (substN i r arg) nm cas (substN i r cin) (substN (i + len) r ret) branches'
      where
        branches' = map (substN i r) branches
        len = length (name cas ++ name cin)

instance SubstTerm CaseIn where
  substN i r (CaseIn binds nmInd args) =
    CaseIn (substN i r binds) nmInd (map (substN (i + ctxLen binds) r) args)

instance SubstTerm Branch where
  substN i r (Branch nm cid xs body whSubst) =
    Branch nm cid xs (substN (i + length xs) r body) (substN (i + length xs) r whSubst)

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
  isFree k Nothing = False
  isFree k (Just c) = isFree k c

  fvN = maybe [] . fvN

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
  isFree k (Meta _) = False
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
  fvN k (Meta _) = []
  fvN k (Ind _ _ ps) = concatMap (fvN k) ps
  fvN k (Constr _ _ ps) = concatMap (fvN k) ps
  fvN k (Fix f) = fvN k f

instance IsFree FixTerm where
  isFree k (FixTerm _ _ _ bs tp body) = isFree k (mkPi bs tp) || isFree (k+1) body

  fvN k (FixTerm _ _ _ bs tp body) = fvN k (mkPi bs tp) ++ fvN (k + 1) body


instance IsFree CaseTerm where
  isFree k (CaseTerm arg _ _ cin tpRet branches) =
    isFree k arg || isFree k tpRet || isFree k cin || any (isFree k) branches

  fvN k (CaseTerm arg _ _ cin tpRet branches) =
    fvN k arg ++ fvN k tpRet ++ fvN k cin ++ concatMap (fvN k) branches

instance IsFree CaseIn where
  isFree k (CaseIn binds _ args) = isFree k binds ||
                                   any (isFree (k + size binds)) args

  fvN k (CaseIn binds _ args) = fvN k binds ++ fvN (k + size binds) args

instance IsFree Branch where
  isFree k (Branch _ _ nmArgs body whSubst) =
    isFree (k + length nmArgs) body || isFree (k + length nmArgs) whSubst

  fvN k (Branch _ _ nmArgs body whSubst) = fvN k1 body ++ fvN k1 whSubst
                                           where k1 = k + length nmArgs

instance IsFree Subst where
  isFree k (Subst sg) = any (isFree k . snd) sg

  fvN k (Subst sg) = concatMap (fvN k . snd) sg

instance IsFree Bind where
  isFree k b = isFree k (bindType b) || isFree k (bindDef b)

  fvN k b = fvN k (bindType b) ++ fvN k (bindDef b)

instance IsFree a => IsFree (Ctx a) where
  isFree k CtxEmpty = False
  isFree k (x :> xs) = isFree k x || isFree (k+1) xs

  fvN k CtxEmpty = []
  fvN k (x :> xs) = fvN k x ++ fvN (k+1) xs
