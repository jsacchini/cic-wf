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
import Utils.Impossible

import qualified Data.Foldable as Fold
import Data.Function
import Data.List

import Text.PrettyPrint

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
    | Constr Name (Name, Int) [Term] [Term]
    | Fix FixTerm
    | Case CaseTerm
    | Ind Annot Name

type Type = Term


mkPi :: Context -> Term -> Term
mkPi ctx t | ctxIsNull ctx = t
           | otherwise = case t of
                           Pi ctx2 t' -> Pi (ctx +: ctx2) t'
                           _          -> Pi ctx t


unPi :: Term -> (Context, Term)
unPi (Pi c t) = (c +: c', t')
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
                            Lam ctx2 t' -> Lam (ctx +: ctx2) t'
                            _           -> Lam ctx t


unLam :: Term -> (Context, Term)
unLam (Lam c t) = (c +: c', t')
  where (c', t') = unLam t
unLam t = (ctxEmpty, t)


-- | Meta variables

newtype MetaVar = MetaVar Int
                  deriving(Eq, Enum, Num, Ord)

instance Show MetaVar where
  show (MetaVar k) = show k

instance Pretty MetaVar where
  prettyPrint (MetaVar k) = text "?" <> int k


-- | Universes

data Sort = Prop
          | Type SortVar
          deriving(Show)

newtype SortVar = SortVar Int
                  deriving(Show, Eq, Enum, Num)


instance Pretty SortVar where
  prettyPrint (SortVar k) = text "u" <> int k


instance Eq Sort where
  s1 == s2 = True -- TODO: fix this. Check typechecking of constructors


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
renameCtx (CtxExtend b bs) (x:xs) =
  CtxExtend (b { bindName = x}) (renameCtx bs xs)


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
                deriving(Show)--,Eq)


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
                 } deriving(Show)

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
  deriving(Show)

isConstr :: Global -> Bool
isConstr (Constructor {}) = True
isConstr _                = False


-- | Equality on terms is only used in the reification to terms, to group
-- contiguous bindings with the same type
-- instance Eq Term where
--   (Sort s1) == (Sort s2) = s1 == s2
--   (Pi c1 t1) == (Pi c2 t2) = c1 == c2 && t1 == t2
--   (Bound n1) == (Bound n2) = n1 == n2
--   (Var x1) == (Var x2) = x1 == x2
--   (Lam c1 t1) == (Lam c2 t2) = c1 == c2 && t1 == t2
--   (App f1 ts1) == (App f2 ts2) = length ts1 == length ts2 &&
--                                  all (uncurry (==)) (zip ts1 ts2) &&
--                                  f1 == f2
--   (Constr _ x1 cid1 ps1 as1) == (Constr _ x2 cid2 ps2 as2) =
--     x1 == x2 && cid1 == cid2 && ps1 == ps2 && as1 == as2
--   (Fix n1 x1 c1 tp1 body1) == (Fix n2 x2 c2 tp2 body2) =
--     n1 == n2 && x1 == x2 && c1 == c2 && tp1 == tp2 && body1 == body2
--   (Case c1) == (Case c2) = c1 == c2
--   (Ind a1 i1) == (Ind a2 i2) = i1 == i2
--   _ == _ = False



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
      mSize (Constr nm cid pars args) = Constr nm cid (map mSize pars) (map mSize args)
      mSize (Fix c) = Fix (modifySize f c)
      mSize (Case c) = Case (modifySize f c)
      mSize (Ind a x) = Ind (f a) x

  listAnnot t@(Sort _) = []
  listAnnot (Pi c t) = listAnnot c ++ listAnnot t
  listAnnot t@(Bound _) = []
  listAnnot t@(Var _) = []
  listAnnot (Lam c t) = listAnnot c ++ listAnnot t
  listAnnot (App t ts) = listAnnot t ++ listAnnot ts
  listAnnot t@(Meta _) = []
  listAnnot (Constr _ _ pars args) = listAnnot pars ++ listAnnot args
  listAnnot (Fix c) = listAnnot c
  listAnnot (Case c) = listAnnot c
  listAnnot (Ind a x) = case a of
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
  lift k n (CtxExtend x xs) = CtxExtend (lift k n x) (lift k (n+1) xs)

instance Lift Term where
  lift _ _ t@(Sort _) = t
  lift k n (Pi c t) = Pi (lift k n c) (lift k (n + ctxLen c) t)
  lift k n t@(Bound m) = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _) = t
  lift k n (Lam c u) = Lam (lift k n c) (lift k (n + ctxLen c) u)
  lift k n (App t1 t2) = App (lift k n t1) $ map (lift k n) t2
  lift k n t@(Meta _) = t
  lift _ _ t@(Ind _ _) = t
  lift k n (Constr x indId ps as) = Constr x indId ps' as'
                                      where ps' = map (lift k n) ps
                                            as' = map (lift k n) as
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
  substN n r (CtxExtend x xs) = CtxExtend (substN n r x) (substN (n+1) r xs)

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
  substN _ _ t@(Ind _ _) = t
  substN i r (Constr x ind ps as) = Constr x ind ps' as'
                                    where ps' = map (substN i r) ps
                                          as' = map (substN i r) as
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
  isFree _ (Ind _ _) = False
  isFree k (Constr _ _ ps as) = any (isFree k) (ps ++ as)
  isFree k (Fix f) = isFree k f
  isFree k (Case c) = isFree k c

  fvN _ (Sort _) = []
  fvN k (Pi c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (Bound n) = if n < k then [] else [n]
  fvN _ (Var _) = []
  fvN k (Lam c t) = fvN k c ++ shiftFV (ctxLen c) (fvN k t)
  fvN k (App f ts) = fvN k f ++ concatMap (fvN k) ts
  fvN k (Meta _) = []
  fvN _ (Ind _ _) = []
  fvN k (Constr _ _ ps as) = concatMap (fvN k) (ps ++ as)
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
  isFree k (CtxExtend x xs) = isFree k x || isFree (k+1) xs

  fvN k CtxEmpty = []
  fvN k (CtxExtend x xs) = fvN k x ++ fvN (k+1) xs




------------------------------------------------------------
-- The Show instances below are used only for debugging.
--
-- Pretty printing of 'Term' is done through the module
-- Syntax.InternaltoAbstract
------------------------------------------------------------

deriving instance Show Term
deriving instance Show CaseTerm
deriving instance Show FixTerm
deriving instance Show CaseIn
deriving instance Show Branch

-- instance Show a => Show (Ctx a) where
--   show Empctx = ""
--   show (Consctx b c) = show b ++ show c

instance Show Bind where
  show b = showImplicit b $ concat [ show (bindName b)
                                   , showDef (bindDef b)
                                   , show (bindType b)]
    where
      showDef Nothing = ""
      showDef (Just x) = " := " ++ show x

-- instance Show Term where
--   show (Sort s) = show s
--   show (Pi bs e) = concat $ "Pi " : map show bs ++ [", ", show e]
--   show (Bound n) = concat ["[", show n, "]"]
--   show (Var x) = show x
--   show (Lam bs e) = concat $ "fun " : map show bs ++ [" => ", show e]
--   show (App e1 es) = "App " ++ show e1 ++ showArgs es
--     where showArgs [] = ""
--           showArgs (e : es) = concat ["(", show e, ") ", showArgs es]
--   show (Case c) = show c
--   show (Fix n x bs tp body) = concat ["fix ", show n, " ", show x, "..."]
--                               -- show bs,
--                               --        " : ", show tp, " := ", show body]
--   show (Constr x i ps as) = concat $ [show x, " ", -- show i,
--                                       --"(",
--                                       intercalate ", " (map show (ps ++ as))] --, ")"]
--   show (Ind a x) = concat [show x] --, "<", show a, ">"]

-- instance Show CaseTerm where
--   show (CaseTerm arg nm tp branches) =
--     concat $ [--"<", show tp, ">",
--               "case ", -- on (", show nm, ")  ",
--               show arg] ++
--               map (("| "++) . show) branches

-- instance Show Branch where
--   show (Branch nm cid args body) =
--     concat [show nm, " : ", show args, " => ", show body]

-- instance Show Global where
--   show (Assumption tp) = "assume " ++ show tp
--   show (Inductive pars indices sort constr) =
--     concat $ [show pars, " : ", show indices, " -> ", show sort,
--               " := "] ++ map show constr
--   show (Constructor name cid pars args indices) =
--     concat [" | ", show name, " : ", show pars, " ", show args, " --> ",
--             show indices]
--   show (Definition t1 t2) = "define : " ++ show t1 ++ " := " ++ show t2
