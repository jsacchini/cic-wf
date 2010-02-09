{-# LANGUAGE PackageImports, FlexibleContexts, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances
 #-}
{-# LANGUAGE CPP #-}

module Syntax.Scope where

#include "../undefined.h"
import Utils.Impossible

import "mtl" Control.Monad.Reader

import Data.List

import Environment
import Syntax.Abstract
import Syntax.Global
import Kernel.TCM


scope :: (MonadGE m, MonadReader [Name] m) => Expr -> m Expr
scope (Ann p e1 e2) = do s1 <- scope e1
                         s2 <- scope e2
                         return $ Ann p s1 s2
scope (Pi p x e1 e2) = do s1 <- scope e1
                          s2 <- local (x:) $ scope e2
                          return $ Pi p x s1 s2
scope (Lam p x e1 e2) = do s1 <- scope e1
                           s2 <- local (x:) $ scope e2
                           return $ Lam p x s1 s2
scope (App p e1 e2) = do s1 <- scope e1
                         s2 <- scope e2
                         return $ App p s1 s2
scope (Var p x) = do l <- ask
                     case findIndex (==x) l of
                       Just n -> return $ Bound p n
                       Nothing -> return $ Var p x
                                  -- do def <- lookupGE x
                                  --    case def of 
                                  --      Just (IndDef _ _ _) -> return $ Ind p x
                                  --      _ -> return $ Var p x -- we should throw an error here, if not found
scope t@(TSort _ _) = return t
scope t@(EVar _ _) = return t
scope t@(Bound _ _) = __IMPOSSIBLE__
scope t@(Ind _ _) = __IMPOSSIBLE__
