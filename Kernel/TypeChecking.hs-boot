{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses,
    TypeSynonymInstances, FlexibleInstances, FlexibleContexts
  #-}

module Kernel.TypeChecking where

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Internal

import Kernel.TCM

class Infer a b | a -> b where
  infer :: (MonadTCM tcm) => a -> tcm b

class Check a b c | a -> b c where
  check :: (MonadTCM tcm) => a -> b -> tcm c


instance Infer A.Bind ([Bind], Sort)

instance (Infer a ([Bind], Sort)) => Infer [a] ([Bind], Sort)

instance Infer A.Expr (Term, Type)

instance Check A.Expr Type Term

isSort :: (MonadTCM tcm) => Term -> tcm Sort
