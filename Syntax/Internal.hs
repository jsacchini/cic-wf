{-# LANGUAGE CPP, FlexibleInstances
  #-}

-- | Internal representation of Terms

module Syntax.Internal where

#include "../undefined.h"
import Utils.Impossible

import Syntax.Common

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
    | Bound Int  -- name is a hint
    | Var Name
    | Lam [Bind] Term
    | App Term [Term]
    -- | Meta MetaId Shift CxtSize
    | Constr Name (Name, Int) [Term] [Term]
    | Fix Int Name [Bind] Type Term
    | Case CaseTerm
    | Ind Name
    deriving(Show)

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
  (Ind i1) == (Ind i2) = i1 == i2
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
  deriving(Show)

mkBindsSameType_ :: [Name] -> Type -> Int -> [Bind]
mkBindsSameType_ [] _ _ = []
mkBindsSameType_ (x:xs) t k = Bind x (lift k 0 t) :
                              mkBindsSameType_ xs t (k + 1)

mkBindsSameType :: [Name] -> Type -> [Bind]
mkBindsSameType xs t = mkBindsSameType_ xs t 0

bind :: Bind -> Type
bind = bindType

bindNoName :: Type -> Bind
bindNoName = Bind noName

instance Eq Bind where
  (Bind _ t1) == (Bind _ t2) = t1 == t2
  (LocalDef _ t1 t2) == (LocalDef _ t3 t4) = t1 == t3 && t2 == t4
  _ == _ = False

class HasType a where
  getType :: a -> Type


data Global = Definition Type Term
            | Assumption Type
            | Inductive {
              indPars :: [Bind],
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
              }
              deriving(Show)

instance HasType Global where
  getType (Definition t _) = t
  getType (Assumption t) = t
  getType i@(Inductive {}) = Pi (indPars i ++ indIndices i) (Sort (indSort i))
  getType c@(Constructor {}) = Pi (constrPars c ++ constrArgs c) ind
    where ind = App (Ind (constrInd c)) (par ++ indices)
          par = map (Var . bindName) (constrPars c)
          indices = constrIndices c


class Lift a where
  lift :: Int -> Int -> a -> a

instance Lift Bind where
  lift k n (Bind x t) = Bind x (lift k n t)
  lift k n (LocalDef x t1 t2) = LocalDef x (lift k n t1) (lift k n t2)

instance Lift Term where
  lift _ _ t@(Sort _) = t
  lift k n (Pi bs t) = Pi (map (lift k n) bs) (lift k (n + 1) t)
  lift k n t@(Bound m) = if m < n then t else Bound (m + k)
  lift _ _ t@(Var _) = t
  lift k n (Lam b u) = Lam (fmap (lift k n) b) (lift k (n + 1) u)
  lift k n (App t1 t2) = App (lift k n t1) $ map (lift k n) t2
  lift _ _ t@(Ind _) = t
  lift k n (Constr x indId ps as) = Constr x indId ps' as'
                                      where ps' = map (lift k n) ps
                                            as' = map (lift k n) as
  lift _ _ _ = error "Complete lift"
-- lift k n t@(Meta i m s) = if m < n then t else Meta i (m+k) s
  -- lift k n (Constr c x ps as) = Constr c x (map (lift k n) ps) (map (lift k n) as)
  -- lift k n (Fix m x bs t e) = Fix m x (liftCxt (flip lift n) k bs) (lift k (n+cxtSize bs) t) (lift k (n+1) e)

class SubstTerm a where
  subst :: Term -> a -> a
  substN :: Int -> Term -> a -> a

  substN = error "Defaul impl of SubstTerm"  -- REMOVE THIS!
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
  substN _ _ t@(Ind _) = t
  substN i r (Constr x ind ps as) = Constr x ind ps' as'
                                    where ps' = map (substN i r) ps
                                          as' = map (substN i r) as
  substN _ _ _ = error "Complete substN"
      -- substN i r t@(Meta _ _ _) = t
      -- substN i r (Constr c x ps as) = Constr c x (map (substN i r) ps) (map (substN i r) as)
      -- substN i r (Fix n x bs t e) = Fix n x (substCxt_ i r bs) (substN (i+cxtSize bs) r t) (substN (i+1) r e)


applyTerms :: [Bind] -> Term -> [Term] -> Term
applyTerms [] body [] = body
applyTerms [] body args = App body args
applyTerms binds body [] = Lam binds body
applyTerms (Bind _ _:bs) body (a:as) = applyTerms (subst a bs) (substN (length bs) a body) as
applyTerms (LocalDef _ _ _:_) _ _ = __IMPOSSIBLE__


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
