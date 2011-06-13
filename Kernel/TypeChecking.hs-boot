{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses,
    TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
    UndecidableInstances
  #-}

module Kernel.TypeChecking where

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Internal

import Kernel.TCM


inferBinds :: (MonadTCM tcm) => [A.Bind] -> tcm (Context, Sort)

infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)

check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term

isSort :: (MonadTCM tcm) => Term -> tcm Sort
