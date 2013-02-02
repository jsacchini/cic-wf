{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

{-# LANGUAGE CPP
  #-}

-- | Scope checking of Declaration and Expr.
--
-- It replaces
-- * Var x           --> Bound n  for bound variables
-- * Var i           --> Ind i    for inductive types
-- * App (Var c ...) --> Constr c j ...   for constructors, checking they are
--                                        fully applied
--
-- We also check that names of global declarations are not defined

module Syntax.Scope(scope) where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader
import Control.Exception

import Data.Function
import Data.List
import Data.Traversable (traverse)

import qualified Syntax.Abstract as A
import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Syntax.Size

import Kernel.TCM

import Utils.Misc
import Utils.Sized

wrongArg :: (MonadTCM tcm) => Range -> Name -> Int -> Int -> tcm a
wrongArg r x m n = typeError $ WrongNumberOfArguments r x m n

undefinedName :: (MonadTCM tcm) => Range -> Name -> tcm a
undefinedName r x = typeError $ UndefinedName r x

constrNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
constrNotApplied r x = typeError $ ConstructorNotApplied r x

-- | We reuse the type-checking monad for scope checking
class Scope a where
  scope :: MonadTCM m => a -> m a

instance Scope A.Bind where
  scope (A.Bind r impl xs e) = fmap (A.Bind r impl xs) (scope e)

instance (Scope a, HasNames a) => Scope [a] where
  scope [] = return []
  scope (x:xs) = do s <- scope x
                    ss <- fakeBinds x $ scope xs
                    return (s:ss)


instance Scope A.Expr where
  scope (A.Ann r e1 e2) =
    do e1' <- scope e1
       e2' <- scope e2
       return $ A.Ann r e1' e2'
  scope t@(A.Sort _ _) = return t
  -- scope t@(EVar _ _) = return t
  scope (A.Pi r bs e) =
    do bs' <- scope bs
       e' <- fakeBinds bs $ scope e
       return $ A.Pi r bs' e'
  scope (A.Arrow r e1 e2) =
    do e1' <- scope e1
       e2' <- fakeBinds noName $ scope e2
       return $ A.Arrow r e1' e2'
  scope (A.Lam r bs e) =
    do bs' <- scope bs
       e' <- fakeBinds bs $ scope e
       return $ A.Lam r bs' e'
  scope t@(A.App _ _ _) =
    do args' <- mapM scope args
       scopeApp func args'
      where
        (func, args) = A.destroyApp t
  scope t@(A.Meta _ _) = return t
  scope t@(A.Ident r x) =
    do xs <- getLocalNames
       case findIndex (==x) xs of
         Just n -> return $ A.Bound r x n
         Nothing ->
           do g <- lookupGlobal x
              case g of
                Just (I.Inductive {}) -> return $ A.Ind r Empty x
                Just c@(I.Constructor {}) ->
                  do when (numArgs /= 0) $ constrNotApplied r x
                     return $ A.Constr r x indId [] []
                    where numArgs = size (I.constrPars c) +
                                    size (I.constrArgs c)
                          indId = (I.constrInd c, I.constrId c)
                Just _ -> return t
                Nothing -> undefinedName r x
  scope (A.Case c) = fmap A.Case (scope c)
  scope (A.Fix f) = fmap A.Fix (scope f)
  -- Ind can appear after parsing for position types (only annotated with star)
  -- We just check that the identifier is actually an inductive type
  scope e@(A.Ind r Star x) =
    do g <- lookupGlobal x
       case g of
         Just (I.Inductive {}) -> return e
         Just _                -> typeError $ NotInductive x
         Nothing               -> typeError $ UndefinedName r x
  scope (A.Ind _ _ _) = __IMPOSSIBLE__
  scope (A.Constr _ _ _ _ _) = __IMPOSSIBLE__
  scope (A.Bound _ _ _) = __IMPOSSIBLE__
  scope (A.Number r n) = scope $ mkNat n
    where mkNat 0 = A.Ident r (Id "O")
          mkNat k = A.App r (A.Ident r (Id "S")) (mkNat (k-1))


instance Scope A.FixExpr where
  scope (A.FixExpr r a recArg x tp body) =
    do when (a == I && recArg <= 0) $ throw $ FixRecursiveArgumentNotPositive r
       tp' <- scope tp
       body' <- fakeBinds x $ scope body
       return $ A.FixExpr r a recArg x tp' body'


instance Scope A.CaseExpr where
  scope (A.CaseExpr r arg asName inName subst ret bs) =
    do arg'    <- scope arg
       inName' <- scope inName
       ret'    <- fakeBinds inName $ fakeBinds asName $ scope ret
       bs'     <- mapM (fakeBinds inName . scope) bs
       let sortbs = sortBy (compare `on` A.brConstrId) bs'
       return $ A.CaseExpr r arg' asName inName' subst ret' sortbs

instance Scope A.CaseIn where
  scope (A.CaseIn r bs ind args) =
    do bs' <- scope bs
       g <- lookupGlobal ind
       case g of
         Just (I.Inductive {}) -> do args' <- mapM (fakeBinds bs . scope) args
                                     return $ A.CaseIn r bs' ind args'
         Just _                -> throw $ NotInductive ind
         Nothing               -> throw $ UndefinedName noRange ind


-- TODO: check that all branch belong to the same inductive type, and that all
--       constructors of the inductive type are considered
instance Scope A.Branch where
  scope (A.Branch r name _ pattern body whSubst) =
    do g <- lookupGlobal name
       case g of
         Just (I.Constructor _ idConstr _ targs _ _) ->
           do when (lenPat /= lenArgs) $ wrongArg r name lenPat lenArgs
              body' <- fakeBinds pattern $ scope body
              whSubst' <- fakeBinds pattern $ traverse (scopeSubst (length pattern)) whSubst
              return $ A.Branch r name idConstr pattern body'
                (fmap A.sortSubst whSubst')
             where lenPat  = length pattern
                   lenArgs = size targs
         Just _ -> throw $ PatternNotConstructor name
         Nothing -> throw $ UndefinedName r name

scopeAssign :: (MonadTCM tcm) => Int -> A.Assign -> tcm A.Assign
scopeAssign k an = do xs <- getLocalNames
                      case findIndex (==A.assgnName an) xs of
                        Just n | n < k -> do e' <- scope (A.assgnExpr an)
                                             return $ an { A.assgnBound = n,
                                                           A.assgnExpr = e' }
                               | otherwise -> error "scope: assign var out of bound"
                        Nothing -> error "scope: var not found"

scopeSubst :: (MonadTCM tcm) => Int -> A.Subst -> tcm A.Subst
scopeSubst k (A.Subst sg) = mapM (scopeAssign k) sg >>= return . A.Subst


scopeApp :: (MonadTCM tcm) => A.Expr -> [A.Expr] -> tcm A.Expr
scopeApp e@(A.Ident r x) args =
  do xs <- getLocalNames
     case findIndex (==x) xs of
       Just n -> return $ A.buildApp (A.Bound r x n) args
       Nothing ->
         do g <- lookupGlobal x
            case g of
              Just (I.Inductive {}) -> return $ A.buildApp (A.Ind r Empty x) args
              Just (I.Constructor i idConstr parsTp argsTp _ _) ->
                  if expLen /= givenLen
                  then wrongArg cRange x expLen givenLen
                  else return $ A.Constr cRange x (i,idConstr) cpars cargs
                where
                  parLen = size parsTp
                  argLen = size argsTp
                  givenLen = length args
                  expLen = parLen + argLen
                  (cpars, cargs) = splitAt parLen args
                  cRange = fuseRange r args
              Just _ -> return $ A.buildApp e args
              Nothing -> undefinedName r x
scopeApp e args = do e' <- scope e
                     return $ A.buildApp e' args


instance (Scope a) => Scope (Maybe a) where
    scope (Just x) = do s <- scope x
                        return $ Just s
    scope Nothing = return Nothing


instance Scope A.Declaration where
    scope (A.Definition r x t u) =
      do t' <- scope t
         u' <- scope u
         checkIfDefined x
         return $ A.Definition r x t' u'
    scope (A.Assumption r x t) =
      do t' <- scope t
         checkIfDefined x
         return $ A.Assumption r x t'
    scope (A.Inductive r indDef) = fmap (A.Inductive r) (scope indDef)
    scope (A.Eval e) =
      do e' <- scope e
         return $ A.Eval e'
    scope (A.Check e1 e2) =
      do e1' <- scope e1
         e2' <- scope e2
         return $ A.Check e1' e2'

instance Scope A.InductiveDef where
  scope (A.InductiveDef x k ps e cs) =
      do ps' <- scope ps
         e'  <- fakeBinds ps $ scope e
         cs' <- fakeBinds ps $ fakeBinds x $ mapM scope cs
         checkIfDefined x
         return $ A.InductiveDef x k ps' e' cs'

instance Scope A.Parameter where
  scope (A.Parameter r np e) = fmap (A.Parameter r np) (scope e)


instance Scope A.Constructor where
  scope (A.Constructor r x e idConstr) =
    do e' <- scope e
       checkIfDefined x
       return (A.Constructor r x e' idConstr)
