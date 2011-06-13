{-# LANGUAGE CPP, FlexibleInstances, StandaloneDeriving
  #-}

-- | Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Data.List
import qualified Data.Foldable as Fold
import Data.Monoid

import Syntax.Common
import Syntax.Size

import Utils.Misc

data Term
    = Sort Sort
    | Pi Context Term
    | Bound Int
    | Var Name
    | Lam Context Term
    | App Term [Term]
    | Constr Name (Name, Int) [Term] [Term]
    | Fix Int Name Context Type Term
    | Case CaseTerm
    | Ind Annot Name

type Type = Term

data Bind =
  Bind {
    bindName :: Name,
    bindType :: Type
    }
  | LocalDef {
    bindName :: Name,
    bindDef :: Term,
    bindType ::Type
    }

unNamed :: Type -> Bind
unNamed = Bind noName

data Ctx a = EmptyCtx
           | ExtendCtx a (Ctx a)

-- | A Context is isomorphic to a list of binds. The reason why we do not simply
--   use a list is that instances such as (shift, subst, isfree) are not simply
--   mappings on the elements, since we have to take care of bound variables
type Context = Ctx Bind

instance Functor Ctx where
  fmap f EmptyCtx = EmptyCtx
  fmap f (ExtendCtx x c) = ExtendCtx (f x) (fmap f c)

instance Fold.Foldable Ctx where
  foldr f r EmptyCtx = r
  foldr f r (ExtendCtx x c) = f x (Fold.foldr f r c)

  foldMap _ EmptyCtx = mempty
  foldMap f (ExtendCtx b c) = f b `mappend` Fold.foldMap f c

(+:) :: Context -> Context -> Context
EmptyCtx +: c2 = c2
(ExtendCtx b c1) +: c2 = ExtendCtx b (c1 +: c2)

empCtx :: Context
empCtx = EmptyCtx

ctxLen :: Context -> Int
ctxLen EmptyCtx = 0
ctxLen (ExtendCtx _ c) = 1 + ctxLen c

(<|) :: Bind -> Context -> Context
(<|) = ExtendCtx

(|>) :: Context -> Bind -> Context
EmptyCtx |> b = ExtendCtx b EmptyCtx
(ExtendCtx b' c') |> b = ExtendCtx b' (c' |> b)

ctxHd :: Context -> Bind
ctxHd (ExtendCtx b _) = b

ctxTl :: Context -> Context
ctxTl (ExtendCtx _ c) = c

instance Eq a => Eq (Ctx a) where
  EmptyCtx == EmptyCtx = True
  (ExtendCtx b1 c1) == (ExtendCtx b2 c2) = b1 == b2 && c1 == c2
  _ == _ = False

data CaseTerm = CaseTerm {
  caseArg :: Term,
  caseNmInd :: Name,
  caseTpRet :: Type,
  caseBranches :: [Branch]
  } deriving(Eq)


data Branch = Branch {
  brName :: Name,
  brConstrId :: Int,
  brArgNames :: [Name],
  brBody :: Term,
  brSubst :: Maybe Subst
  } deriving(Eq)

newtype Subst = Subst { unSubst :: [(Int, Term)] }
                deriving(Show,Eq)

mkPi :: Context -> Term -> Term
mkPi EmptyCtx t = t
mkPi c1 (Pi c2 t) = Pi (c1 +: c2) t
mkPi bs t = Pi bs t

unPi :: Term -> (Context, Term)
unPi (Pi c t) = (c +: c', t')
  where (c', t') = unPi t
unPi t = (empCtx, t)

mkApp :: Term -> [Term] -> Term
mkApp t [] = t
mkApp (App t ts) ts' = App t (ts ++ ts')
mkApp t ts = App t ts

unApp :: Term -> (Term, [Term])
unApp (App t ts) = (func, args++ts)
  where (func, args) = unApp t
unApp t = (t, [])

mkLam :: Context -> Term -> Term
mkLam EmptyCtx t = t
mkLam c1 (Lam c2 t) = Lam (c1 +: c2) t
mkLam c t = Lam c t

unLam :: Term -> (Context, Term)
unLam (Lam c t) = (c +: c', t')
  where (c', t') = unLam t
unLam t = (empCtx, t)

-- flatten :: Term -> Term
-- flatten (Pi bs t) = Pi (bs ++ bs') t'
--                     where (bs', t') = unPi t
-- flatten (Lam bs t) = Lam (bs ++ bs') t'
--                      where (bs', t') = unLam t
-- flatten (App t ts) = App func (args ++ ts)
--                      where (func, args) = findArgs t
-- flatten t = t


data Global = Definition Type Term
            | Assumption Type
            | Inductive {
              indPars :: Context,
              indPol :: [Polarity],
              indIndices :: Context,
              indSort :: Sort,
              indConstr :: [Name]
              }
            | Constructor {
              constrInd :: Name,
              constrId :: Int,   -- id
              constrPars :: Context, -- parameters, should be the same as
                                    -- the indutive type
              constrArgs :: Context, -- arguments
              constrIndices :: [Term]
              } deriving(Show)


-- | Equality on terms is only used in the reification to terms, to group
-- contiguous bindings with the same type
instance Eq Term where
  (Sort s1) == (Sort s2) = s1 == s2
  (Pi c1 t1) == (Pi c2 t2) = c1 == c2 && t1 == t2
  (Bound n1) == (Bound n2) = n1 == n2
  (Var x1) == (Var x2) = x1 == x2
  (Lam c1 t1) == (Lam c2 t2) = c1 == c2 && t1 == t2
  (App f1 ts1) == (App f2 ts2) = length ts1 == length ts2 &&
                                 all (uncurry (==)) (zip ts1 ts2) &&
                                 f1 == f2
  (Constr x1 cid1 ps1 as1) == (Constr x2 cid2 ps2 as2) =
    x1 == x2 && cid1 == cid2 && ps1 == ps2 && as1 == as2
  (Fix n1 x1 c1 tp1 body1) == (Fix n2 x2 c2 tp2 body2) =
    n1 == n2 && x1 == x2 && c1 == c2 && tp1 == tp2 && body1 == body2
  (Case c1) == (Case c2) = c1 == c2
  (Ind a1 i1) == (Ind a2 i2) = i1 == i2
  _ == _ = False





class HasBind a where
  getBind :: a -> Bind

instance HasBind Bind where
  getBind = id

instance HasBind (Polarized Bind) where
  getBind = unPol


bind :: Bind -> Type
bind = bindType

bindNoName :: Type -> Bind
bindNoName = Bind noName

instance Eq Bind where
  (Bind _ t1) == (Bind _ t2) = t1 == t2
  (LocalDef _ t1 t2) == (LocalDef _ t3 t4) = t1 == t3 && t2 == t4
  _ == _ = False



------------------------------------------------------------
-- * Operations on sizes
------------------------------------------------------------

class HasAnnot a where
  modifySize :: (Annot -> Annot) -> a -> a
  eraseSize :: a -> a
  eraseStage :: Int -> a -> a
--  getSizes :: a -> [Size]

  eraseSize = modifySize $ const Empty
  eraseStage i = modifySize f
    where f Empty    = Empty
          f Star     = Star
          f (Size s) = case base s of
                         Just j | i == j    -> Star
                                | otherwise -> Empty
                         Nothing            -> Empty

instance HasAnnot a => HasAnnot (Maybe a) where
  modifySize = fmap . modifySize

instance HasAnnot Term where
  modifySize f = mSize
    where
      mSize t@(Sort _) = t
      mSize (Pi c t) = Pi (modifySize f c) (mSize t)
      mSize t@(Bound _) = t
      mSize t@(Var _) = t
      mSize (Lam c t) = Lam (modifySize f c) (mSize t)
      mSize (App t ts) = App (mSize t) (map mSize ts)
      mSize (Constr nm cid pars args) = Constr nm cid (map mSize pars) (map mSize args)
      mSize (Fix n x c t1 t2) = Fix n x (modifySize f c) (mSize t1) (mSize t2)
      mSize (Case c) = Case (modifySize f c)
      mSize (Ind a x) = Ind (f a) x

instance HasAnnot CaseTerm where
  modifySize f (CaseTerm arg nm ret bs) =
    CaseTerm (modifySize f arg) nm (modifySize f ret) (map (modifySize f) bs)

instance HasAnnot Branch where
  modifySize f (Branch nm cid nmArgs body whSubst) =
    Branch nm cid nmArgs (modifySize f body) (modifySize f whSubst)

instance HasAnnot Subst where
  modifySize f (Subst sg) = Subst $ map (appSnd (modifySize f)) sg

instance HasAnnot Bind where
  modifySize f (Bind nm tp) = Bind nm (modifySize f tp)
  modifySize f (LocalDef nm t1 t2) = LocalDef nm (modifySize f t1) (modifySize f t2)

instance HasAnnot a => HasAnnot (Ctx a) where
  modifySize f c = fmap (modifySize f) c

------------------------------------------------------------
-- * Operations on de Bruijn indices
------------------------------------------------------------

------------------------------------------------------------
-- ** Raise
------------------------------------------------------------


class Lift a where
  lift :: Int -> Int -> a -> a

instance Lift a => Lift (Maybe a) where
  lift k n = fmap (lift k n)

instance Lift Bind where
  lift k n (Bind x t) = Bind x (lift k n t)
  lift k n (LocalDef x t1 t2) = LocalDef x (lift k n t1) (lift k n t2)

instance Lift a => Lift (Ctx a) where
  lift k n EmptyCtx = EmptyCtx
  lift k n (ExtendCtx b c) = ExtendCtx (lift k n b) (lift k (n + 1) c)

instance Lift Term where
  lift _ _ t@(Sort _) = t
  lift k n (Pi c t) = Pi (lift k n c) (lift k (n + ctxLen c) t)
  lift k n t@(Bound m) = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _) = t
  lift k n (Lam c u) = Lam (lift k n c) (lift k (n + ctxLen c) u)
  lift k n (App t1 t2) = App (lift k n t1) $ map (lift k n) t2
  lift _ _ t@(Ind _ _) = t
  lift k n (Constr x indId ps as) = Constr x indId ps' as'
                                      where ps' = map (lift k n) ps
                                            as' = map (lift k n) as
  lift k n (Fix m x c t e) =
    Fix m x (lift k n c) (lift k (n + ctxLen c) t) (lift k (n + 1) e)
  lift k n (Case c) = Case (lift k n c)


instance Lift CaseTerm where
  lift k n (CaseTerm arg nm ret branches) =
    CaseTerm (lift k n arg) nm (lift k n ret) (map (lift k n) branches)

instance Lift Branch where
  lift k n (Branch nm cid nmArgs body whSubst) =
    Branch nm cid nmArgs (lift k (n + length nmArgs) body) (lift k (n + length nmArgs) whSubst)

instance Lift Subst where
  lift k n (Subst sg) = Subst $ map (appSnd (lift k n)) sg

------------------------------------------------------------
-- ** Substitution
------------------------------------------------------------


class SubstTerm a where
  subst :: Term -> a -> a
  substN :: Int -> Term -> a -> a

  subst = substN 0

instance SubstTerm a => SubstTerm (Maybe a) where
  substN k = fmap . substN k

instance SubstTerm [Term] where
  substN n r = map (substN n r)

instance SubstTerm Bind where
  substN n r (Bind x t) = Bind x (substN n r t)
  substN n r (LocalDef x t1 t2) =
    LocalDef x (substN n r t1) (substN n r t2)

instance SubstTerm a => SubstTerm (Ctx a) where
  substN n r EmptyCtx = EmptyCtx
  substN n r (ExtendCtx b c) = ExtendCtx (substN n r b) (substN (n + 1) r c)

instance SubstTerm Term where
  substN _ _ t@(Sort _) = t
  substN i r (Pi c t) = Pi (substN i r c) (substN (i + ctxLen c) r t)
  substN i r t@(Bound n) | n < i = t
                         | n == i = lift i 0 r
                         | otherwise = Bound (n - 1)
  substN _ _ t@(Var _) = t
  substN i r (Lam c t) = Lam (substN i r c) (substN (i + ctxLen c) r t)
  substN i r (App t ts) = App (substN i r t) (substN i r ts)
  substN _ _ t@(Ind _ _) = t
  substN i r (Constr x ind ps as) = Constr x ind ps' as'
                                    where ps' = map (substN i r) ps
                                          as' = map (substN i r) as
  substN i r (Case c) = Case (substN i r c)
  substN i r (Fix k nm c tp body) =
    Fix k nm (substN i r c) (substN (i + ctxLen c) r tp) (substN (i + 1) r body)


instance SubstTerm CaseTerm where
  substN i r (CaseTerm arg nm ret branches) =
    CaseTerm (substN i r arg) nm (substN i r ret) branches'
      where branches' = map (substN i r) branches

instance SubstTerm Branch where
  substN i r (Branch nm cid xs body whSubst) =
    Branch nm cid xs (substN (i + length xs) r body) (substN (i + length xs) r whSubst)

instance SubstTerm Subst where
  substN i r (Subst sg) = Subst $ map (appSnd (substN i r)) sg



------------------------------------------------------------
-- ** Free bound variables
------------------------------------------------------------

class IsFree a where
  isFree :: Int -> a -> Bool

instance IsFree a => IsFree (Maybe a) where
  isFree k Nothing = False
  isFree k (Just c) = isFree k c

instance IsFree Term where
  isFree _ (Sort _) = False
  isFree k (Pi c t) = isFree k c || isFree (k + ctxLen c) t
  isFree k (Bound n) = k == n
  isFree _ (Var _) = False
  isFree k (Lam c t) = isFree k c || isFree (k + ctxLen c) t
  isFree k (App f ts) = isFree k f || any (isFree k) ts
  isFree _ (Ind _ _) = False
  isFree k (Constr _ _ ps as) = any (isFree k) (ps ++ as)
  isFree k (Fix _ _ bs tp body) = isFree k (mkPi bs tp) || isFree (k+1) body
  isFree k (Case c) = isFree k c

instance IsFree CaseTerm where
  isFree k (CaseTerm arg _ tpRet branches) =
    isFree k arg || isFree k tpRet || any (isFree k) branches

instance IsFree Branch where
  isFree k (Branch _ _ nmArgs body whSubst) =
    isFree (k + length nmArgs) body || isFree (k + length nmArgs) whSubst

instance IsFree Subst where
  isFree k (Subst sg) = any (isFree k . snd) sg

instance IsFree Bind where
  isFree k (Bind _ t) = isFree k t
  isFree k (LocalDef _ t1 t2) = isFree k t1 || isFree k t2

instance IsFree a => IsFree (Ctx a) where
  isFree k EmptyCtx = False
  isFree k (ExtendCtx b c) = isFree k b || isFree (k + 1) c

isFreeList :: Int -> [Term] -> Bool
isFreeList k = foldrAcc (\n t r -> isFree n t || r) (\n _ -> n + 1) k False






------------------------------------------------------------
-- The Show instances below are used only for debugging.
--
-- Pretty printing of 'Term' is done through the module
-- Syntax.InternaltoAbstract
------------------------------------------------------------

deriving instance Show Term
deriving instance Show a => Show (Ctx a)
deriving instance Show CaseTerm
deriving instance Show Branch

instance Show Bind where
  show (Bind x t) = concat ["(",  show x, " : ", show t, ")"]
  show (LocalDef x t1 t2) = concat ["(", show x, " := ", show t1, " : ", show t2]

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
