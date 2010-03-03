{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies
  #-}

module Environment where

import Data.List

import Syntax.Bind
import Syntax.Internal
import Syntax.Name
import Syntax.Global

-- Global environments

class Env e where
    type Elem e
    emptyEnv :: e
    extendEnv :: Name -> Elem e -> e -> e
    bindedEnv :: Name -> e -> Bool
    lookupEnv :: Name -> e -> Maybe (Elem e)
    listEnv :: e -> [(Name, Elem e)]

newtype EnvT a = EnvT { unEnvT :: [(Name, a)] }
                 deriving(Show)

type GlobalEnv = EnvT Global
type LocalEnv a = EnvT (GType a)

instance Env (EnvT a) where
    type Elem (EnvT a) = a
    emptyEnv = EnvT []
    extendEnv n v e = EnvT $ (n,v) : unEnvT e
    bindedEnv n = elem n . map fst . unEnvT
    lookupEnv n = lookup n . unEnvT
    listEnv = unEnvT


