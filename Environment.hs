{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies
  #-}

module Environment where

import Data.List

import Syntax.Internal
import Syntax.ETag

-- Global environments

class Env e where
    type Elem e
    emptyEnv :: e
    extendEnv :: Name -> Elem e -> e -> e
    bindedEnv :: Name -> e -> Bool
    lookupEnv :: Name -> e -> Maybe (Elem e)
    listEnv :: e -> [(Name, Elem e)]

-- type ConstrType = (Name, NamedCxt, [Term])


-- Inductive I Gamma_I : Gamma_a . s := C_i Gamma_i. I ts_i
-- is represented as
-- Ind I Gamma_I Gamma_a s [(C_i, Gamma_i, ts_i)]

-- isInd :: Global -> Bool
-- isInd (Ind _ _ _ _) = True
-- isInd _ = False

class (Monad m) => MonadGE m where
    lookupGE :: Name -> m (Maybe (Global NM))

newtype EnvT a = EnvT { unEnvT :: [(Name, a)] }
                 deriving(Show)

type GlobalEnv a = EnvT (Global a)
type LocalEnv a = EnvT (Type a)

instance Env (EnvT a) where
    type Elem (EnvT a) = a
    emptyEnv = EnvT []
    extendEnv n v e = EnvT $ (n,v) : unEnvT e
    bindedEnv n = elem n . map fst . unEnvT
    lookupEnv n = lookup n . unEnvT
    listEnv = unEnvT


