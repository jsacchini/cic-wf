{-# LANGUAGE CPP, FlexibleInstances
  #-}

-- | Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Data.List

import Syntax.Common
import Syntax.Size

tType :: Int -> Term
tType = Sort . Type
tProp :: Term
tProp = Sort Prop

type MetaId = Int
type Shift = Int
type CxtSize = Int

data Term
    = Sort Sort
    | Pi [Bind] Term
    | Bound Int
    | Var Name
    | Lam [Bind] Term
    | App Term [Term]
    -- | Meta MetaId Shift CxtSize
    | Constr Name (Name, Int) [Term] [Term]
    | Fix Int Name [Bind] Type Term
    | Case CaseTerm
    | Ind Annot Name
    deriving(Show)

-- Returns the constructor id or Nothing if it's not a constructor
isConstr :: Term -> Maybe Int
isConstr (Constr _ (_,cid) _ _) = Just cid
isConstr _                      = Nothing

getConstrArgs (Constr _ _ _ as) = as


data CaseTerm = CaseTerm {
  caseArg :: Term,
  caseNmInd :: Name,
  caseTpRet :: Type,
  caseBranches :: [Branch]
  } deriving(Show)

data Branch = Branch {
  brName :: Name,
  brConstrId :: Int,
  brArgNames :: [Name],
  brBody :: Term
  } deriving(Show)


buildPi :: [Bind] -> Term -> Term
buildPi [] t = t
buildPi bs (Pi bs' t) = Pi (bs ++ bs') t
buildPi bs t = Pi bs t

buildApp :: Term -> [Term] -> Term
buildApp t [] = t
buildApp (App t ts) ts' = App t (ts ++ ts')
buildApp t ts = App t ts

buildLam :: [Bind] -> Term -> Term
buildLam [] t = t
buildLam bs (Lam bs' t) = Lam (bs ++ bs') t
buildLam bs t = Lam bs t

bound :: Int -> Int -> [Term]
bound m n = map Bound [m..n]

dom :: [Bind] -> [Term]
dom bs = reverse $ bound 0 (length bs - 1)

-- | Changes the names of binds (used to print names similar to the ones given
--   by the user.
--
--   Expects lists of the same size.
renameBinds :: [Bind] -> [Name] -> [Bind]
renameBinds [] [] = []
renameBinds (Bind _ t:bs) (x:xs)         = Bind x t : renameBinds bs xs
renameBinds (LocalDef _ t1 t2:bs) (x:xs) = LocalDef x t1 t2 : renameBinds bs xs
renameBinds _ _ = __IMPOSSIBLE__

-- | Equality on terms is only used in the reification to terms, to group
-- contiguous bindings with the same type
instance Eq Term where
  (Sort s1) == (Sort s2) = s1 == s2
  (Pi bs1 t1) == (Pi bs2 t2) = length bs1 == length bs2 &&
                               all (uncurry (==)) (zip bs1 bs2) &&
                               t1 == t2
  (Bound n1) == (Bound n2) = n1 == n2
  (Var x1) == (Var x2) = x1 == x2
  (Lam bs1 t1) == (Lam bs2 t2) = length bs1 == length bs2 &&
                                 all (uncurry (==)) (zip bs1 bs2) &&
                                 t1 == t2
  (App f1 ts1) == (App f2 ts2) = length ts1 == length ts2 &&
                                 all (uncurry (==)) (zip ts1 ts2) &&
                                 f1 == f2
  (Ind a1 i1) == (Ind a2 i2) = a1 == a2 && i1 == i2
  _ == _ = False

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

instance Show Bind where
  show (Bind x t) = concat ["(",  show x, " : ", show t, ")"]
  show (LocalDef x t1 t2) = concat ["(", show x, " := ", show t1, " : ", show t2]


class HasBind a where
  getBind :: a -> Bind

instance HasBind Bind where
  getBind = id

instance HasBind (Polarized Bind) where
  getBind = unPol

mkBindsSameType_ :: [(Name, Polarity)] -> Type -> Int -> [Polarized Bind]
mkBindsSameType_ [] _ _ = []
mkBindsSameType_ ((x,pol):xs) t k = Pol { unPol = Bind x (lift k 0 t),
                                          polarity = pol }:
                                    mkBindsSameType_ xs t (k + 1)

mkBindsSameType :: [(Name, Polarity)] -> Type -> [Polarized Bind]
mkBindsSameType xs t = mkBindsSameType_ xs t 0

bind :: Bind -> Type
bind = bindType

bindNoName :: Type -> Bind
bindNoName = Bind noName

instance Eq Bind where
  (Bind _ t1) == (Bind _ t2) = t1 == t2
  (LocalDef _ t1 t2) == (LocalDef _ t3 t4) = t1 == t3 && t2 == t4
  _ == _ = False


data Global = Definition Type Term
            | Assumption Type
            | Inductive {
              indPars :: [Polarized Bind],
              indIndices :: [Bind],
              indSort :: Sort,
              indConstr :: [Name]
              }
            | Constructor {
              constrInd :: Name,
              constrId :: Int,   -- id
              constrPars :: [Bind], -- parameters, should be the same as
                                    -- the indutive type
              constrArgs :: [Bind], -- arguments
              constrIndices :: [Term]
              } deriving(Show)

-- class HasType a where
--   getType :: a -> Type

-- instance HasType Global where
--   getType (Definition t _) = t
--   getType (Assumption t) = t
--   getType i@(Inductive {}) = Pi (indPars i ++ indIndices i) (Sort (indSort i))
--   getType c@(Constructor {}) = Pi (constrPars c ++ constrArgs c) ind
--     where ind = App (Ind (constrInd c)) (par ++ indices)
--           par = map (Var . bindName) (constrPars c)
--           indices = constrIndices c

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

instance HasAnnot Term where
  modifySize f = mSize
    where
      mSize t@(Sort _) = t
      mSize (Pi bs t) = Pi (map (modifySize f) bs) (mSize t)
      mSize t@(Bound _) = t
      mSize t@(Var _) = t
      mSize (Lam bs t) = Lam (map (modifySize f) bs) (mSize t)
      mSize (App t ts) = App (mSize t) (map mSize ts)
      mSize (Constr nm cid pars args) = Constr nm cid (map mSize pars) (map mSize args)
      mSize (Fix n x bs t1 t2) = Fix n x (map (modifySize f) bs) (mSize t1) (mSize t2)
      mSize (Case c) = Case (modifySize f c)
      mSize (Ind a x) = Ind (f a) x

instance HasAnnot CaseTerm where
  modifySize f (CaseTerm arg nm ret bs) =
    CaseTerm (modifySize f arg) nm (modifySize f ret) (map (modifySize f) bs)

instance HasAnnot Branch where
  modifySize f (Branch nm cid nmArgs body) =
    Branch nm cid nmArgs (modifySize f body)

instance HasAnnot Bind where
  modifySize f (Bind nm tp) = Bind nm (modifySize f tp)
  modifySize f (LocalDef nm t1 t2) = LocalDef nm (modifySize f t1) (modifySize f t2)





class Lift a where
  lift :: Int -> Int -> a -> a

instance Lift Bind where
  lift k n (Bind x t) = Bind x (lift k n t)
  lift k n (LocalDef x t1 t2) = LocalDef x (lift k n t1) (lift k n t2)

instance Lift a => Lift [a] where
  lift k n [] = []
  lift k n (x : xs) = lift k n x : lift k (n + 1) xs

instance Lift Term where
  lift _ _ t@(Sort _) = t
  lift k n (Pi bs t) = Pi (lift k n bs) (lift k (n + length bs) t)
  lift k n t@(Bound m) = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _) = t
  lift k n (Lam bs u) = Lam (lift k n bs) (lift k (n + length bs) u)
  lift k n (App t1 t2) = App (lift k n t1) $ map (lift k n) t2
  lift _ _ t@(Ind _ _) = t
  lift k n (Constr x indId ps as) = Constr x indId ps' as'
                                      where ps' = map (lift k n) ps
                                            as' = map (lift k n) as
  lift k n (Fix m x bs t e) =
    Fix m x (lift k n bs) (lift k (n + length bs) t) (lift k (n + 1) e)
  lift k n (Case c) = Case (lift k n c)


instance Lift CaseTerm where
  lift k n (CaseTerm arg nm ret branches) =
    CaseTerm (lift k n arg) nm (lift k n ret) (map (lift k n) branches)

instance Lift Branch where
  lift k n (Branch nm cid nmArgs body) =
    Branch nm cid nmArgs (lift k (n + length nmArgs) body)


class SubstTerm a where
  subst :: Term -> a -> a
  substN :: Int -> Term -> a -> a

  subst = substN 0

instance SubstTerm [Term] where
  substN n r = map (substN n r)

instance SubstTerm [Bind] where
  substN _ _ [] = []
  substN n r (Bind x t:bs) = Bind x (substN n r t) : substN (n + 1) r bs
  substN n r (LocalDef x t1 t2:bs) =
    LocalDef x (substN n r t1) (substN n r t2) : substN (n + 1) r bs

instance SubstTerm Term where
  substN _ _ t@(Sort _) = t
  substN i r (Pi bs t) = Pi (substN i r bs) (substN (i + len) r t)
                         where len = length bs
  substN i r t@(Bound n) | n < i = t
                         | n == i = lift i 0 r
                         | otherwise = Bound (n - 1)
  substN _ _ t@(Var _) = t
  substN i r (Lam bs t) = Lam (substN i r bs) (substN (i + len) r t)
                          where len = length bs
  substN i r (App t ts) = App (substN i r t) (substN i r ts)
  substN _ _ t@(Ind _ _) = t
  substN i r (Constr x ind ps as) = Constr x ind ps' as'
                                    where ps' = map (substN i r) ps
                                          as' = map (substN i r) as
  substN i r (Case c) = Case (substN i r c)
  substN i r (Fix k nm bs tp body) =
    Fix k nm (substN i r bs) (substN (i + length bs) r tp) (substN (i + 1) r body)


instance SubstTerm CaseTerm where
  substN i r (CaseTerm arg nm ret branches) =
    CaseTerm (substN i r arg) nm (substN i r ret) branches'
      where branches' = map (substN i r) branches

instance SubstTerm Branch where
  substN i r (Branch nm cid xs body) =
    Branch nm cid xs (substN (i + length xs) r body)



flatten :: Term -> Term
flatten (Pi bs t) = Pi (bs ++ bs') t'
                    where (bs', t') = findBindsPi t
flatten (Lam bs t) = Lam (bs ++ bs') t'
                     where (bs', t') = findBindsLam t
flatten (App t ts) = App func (args ++ ts)
                     where (func, args) = findArgs t
flatten t = t

findBindsPi :: Term -> ([Bind], Term)
findBindsPi (Pi bs t) = (bs ++ bs', t')
                        where (bs', t') = findBindsPi t
findBindsPi t = ([], t)

findBindsLam :: Term -> ([Bind], Term)
findBindsLam (Lam bs t) = (bs ++ bs', t')
                          where (bs', t') = findBindsLam t
findBindsLam t = ([], t)

findArgs :: Term -> (Term, [Term])
findArgs (App t ts) = (func, args++ts)
                      where (func, args) = findArgs t
findArgs t = (t, [])




------------------------
--- The instances below are used only for debugging

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
