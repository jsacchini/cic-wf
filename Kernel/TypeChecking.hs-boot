{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses,
    TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
    UndecidableInstances
  #-}

module Kernel.TypeChecking where

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Internal

import Kernel.TCM

maxSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort

inferBinds :: (MonadTCM tcm) => A.Context -> tcm (Context, Sort)

infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)

check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term

checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]

isSort :: (MonadTCM tcm) => Term -> tcm Sort
