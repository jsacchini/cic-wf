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
    = Def Type Term
--    | Ind NamedCxt NamedCxt Sort [ConstrType]
    | Axiom Type
--    deriving(Show)

-- type ConstrType = (Name, NamedCxt, [Term])

-- type NamedCxt = [(Name, Term)]

-- Inductive I Gamma_I : Gamma_a . s := C_i Gamma_i. I ts_i
-- is represented as
-- Ind I Gamma_I Gamma_a s [(C_i, Gamma_i, ts_i)]

-- isInd :: Global -> Bool
-- isInd (Ind _ _ _ _) = True
-- isInd _ = False

class (Monad m) => MonadGE m where
    lookupGE :: Name -> m Global

newtype EnvT a = EnvT { unEnvT :: [(Name, a)] }

type GlobalEnv = EnvT Global
type LocalEnv = EnvT Type

instance Env a (EnvT a) where
    emptyEnv = EnvT []
    extendEnv n v e = EnvT $ (n,v) : unEnvT e
    bindedEnv n = elem n . map fst . unEnvT
    lookupEnv n = lookup n . unEnvT
    listEnv = unEnvT


