{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances
  #-}

module Environment where

import Data.List

import Internal

-- Global environments

class Env v e | e -> v where
    emptyEnv :: e
    extendEnv :: Name -> v -> e -> e
    bindedEnv :: Name -> e -> Bool
    lookupEnv :: Name -> e -> Maybe v
    listEnv :: e -> [(Name, v)]

data Global
    = Def Term Term -- body, type
--    | Ind NamedCxt NamedCxt Sort [ConstrType]
    | Axiom Term -- type
--    deriving(Show)

-- type ConstrType = (Name, NamedCxt, [Term])

type NamedCxt = [(Name, Term)]

-- Inductive I Gamma_I : Gamma_a . s := C_i Gamma_i. I ts_i
-- is represented as
-- Ind I Gamma_I Gamma_a s [(C_i, Gamma_i, ts_i)]

-- isInd :: Global -> Bool
-- isInd (Ind _ _ _ _) = True
-- isInd _ = False

newtype EnvT a = EnvT { unEnvT :: [(Name, a)] }

type GlobalEnv = EnvT Global
type LocalEnv = EnvT Type

instance Env a (EnvT a) where
    emptyEnv = EnvT []
    extendEnv n v e = EnvT $ (n,v) : unEnvT e
    bindedEnv n = elem n . map fst . unEnvT
    lookupEnv n = lookup n . unEnvT
    listEnv = unEnvT

newtype GEnv = MkGE [(Name, Global)] -- id, type, body

emptyGlobal = MkGE []

genvAdd :: GEnv -> Name -> Global -> GEnv
genvAdd (MkGE es) n d = MkGE $ (n,d):es

genvGet :: GEnv -> Name -> Global
genvGet (MkGE []) x = error $ x ++ ": not found"
genvGet (MkGE ((n,d):es)) x = if x == n then d else genvGet (MkGE es) x

-- lookupGlobal :: Name -> GEnv -> Maybe Global
-- lookupGlobal x (MkGE es) = lookup x es

-- lookup_ind :: Name -> GEnv -> Maybe (NamedCxt, NamedCxt, Sort, [ConstrType])
-- lookup_ind x g = case lookup_global x g of
--                    Just (Ind gs as s cs) -> return (gs,as,s,cs)
--                    otherwise -> Nothing

-- lookup_constr :: Name -> GEnv -> Maybe (Name, NamedCxt, NamedCxt, Sort, NamedCxt, [Term])
-- lookup_constr x (MkGE es) = lookup x (concat $ map mapI $ filter (isInd . snd) es)
--                             where mapI (n, Ind gs as s cs) = map (\(a,b,c) -> (a,(n,gs,as,s,b,c))) cs


-- Local environments (for bound variables)

type LEnv = [(Name, Term)] -- types for bound variables

emptyLocal = []

