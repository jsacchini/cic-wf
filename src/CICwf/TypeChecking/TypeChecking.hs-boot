{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

module CICwf.TypeChecking.TypeChecking where

import qualified CICwf.Syntax.Abstract  as A
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.TCM

maxSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort

inferBinds :: (MonadTCM tcm) => A.Context -> tcm (Context, Sort)

inferType :: (MonadTCM tcm) => A.Expr -> tcm (Type, Sort)

infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)

check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term

checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]

isSort :: (MonadTCM tcm) => Range -> Term -> Type -> tcm Sort

checkPattern :: (MonadTCM tcm) => A.Pattern -> Context
                -> tcm (Pattern, Context)
