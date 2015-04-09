{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}

-- | Scope checking of C.Declaration and C.Expr.
--
-- It replaces
-- * Var x           --> Bound n  for bound variables
-- * App (Var i ...) --> Ind i ...     for inductive types, checking they are
--                                     applied to parameters
-- * App (Var c ...) --> Constr c j ...   for constructors, checking they are
--                                        fully applied
--
-- We also check that names of global declarations are not defined

-- TODO: check pattern linearity and constraint type linearity

module CICwf.Syntax.ScopeMonad where

import           CICwf.Utils.Impossible

import           Control.Exception
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Function
import           Data.Functor
import           Data.List
import           Data.Maybe

import qualified CICwf.Syntax.Abstract        as A
import           CICwf.Syntax.Common
import qualified CICwf.Syntax.Concrete        as C
import qualified CICwf.Syntax.Internal        as I
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.TCM

import           CICwf.Utils.Sized


-- | We reuse the type-checking monad for scope checking
--   TODO: maybe move these function somewhere else
class Scope a b | a -> b where
  scope :: MonadTCM m => a -> m b


getScope :: MonadTCM tcm => tcm LocalScope
getScope = stScope <$> get


setScope :: MonadTCM tcm => LocalScope -> tcm ()
setScope s = do
  st <- get
  put $ st { stScope = s }


withScope :: MonadTCM tcm => LocalScope -> tcm a -> tcm a
withScope s = localScope (const s)


localScope :: MonadTCM tcm => (LocalScope -> LocalScope) -> tcm a -> tcm a
localScope f m = do
  s <- getScope
  setScope (f s)
  x <- m
  setScope s
  return x


extendScope :: MonadTCM tcm => [Name] -> tcm a -> tcm a
extendScope s = localScope (\s' -> s' <:> ctxFromList s)


getSizeScope :: MonadTCM tcm => tcm LocalScope
getSizeScope = stSizeScope <$> get


setSizeScope :: MonadTCM tcm => LocalScope -> tcm ()
setSizeScope s = do
  st <- get
  put $ st { stSizeScope = s }


withSizeScope :: MonadTCM tcm => LocalScope -> tcm a -> tcm a
withSizeScope s = localSizeScope (const s)


localSizeScope :: MonadTCM tcm => (LocalScope -> LocalScope) -> tcm a -> tcm a
localSizeScope f m = do
  s <- getSizeScope
  setSizeScope (f s)
  x <- m
  setSizeScope s
  return x


extendSizeScope :: MonadTCM tcm => [Name] -> tcm a -> tcm a
extendSizeScope s = localSizeScope (\s' -> s' <:> ctxFromList s)
