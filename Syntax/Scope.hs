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

import Data.List

import qualified Syntax.Abstract as A
import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Syntax.Size

import Kernel.TCM


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
  scope (A.Bind r xs e) = fmap (A.Bind r xs) (scope e)


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
                    where numArgs = length (I.constrPars c) +
                                    length (I.constrArgs c)
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
  scope t@(A.Number _ _) = return t
  scope (A.Ind _ _ _) = __IMPOSSIBLE__
  scope (A.Constr _ _ _ _ _) = __IMPOSSIBLE__
  scope (A.Bound _ _ _) = __IMPOSSIBLE__


instance Scope A.FixExpr where
  scope (A.FixExpr r recArg x tp body) =
    do when (recArg <= 0) $ throw $ FixRecursiveArgumentNotPositive r
       tp' <- scope tp
       body' <- fakeBinds x $ scope body
       return $ A.FixExpr r recArg x tp' body'


instance Scope A.CaseExpr where
  scope (A.CaseExpr r arg asName inName subst ret bs) =
    do arg'    <- scope arg
       inName' <- scope inName
       ret'    <- fakeBinds asName $ fakeBinds inName $ scope ret
       bs'     <- mapM (fakeBinds inName . scope) bs
       return $ A.CaseExpr r arg' asName inName' subst ret' bs'

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
  scope (A.Branch r name _ pattern body) =
    do g <- lookupGlobal name
       case g of
         Just (I.Constructor _ idConstr _ targs _) ->
           do when (lenPat /= lenArgs) $ wrongArg r name lenPat lenArgs
              body' <- fakeBinds pattern $ scope body
              return $ A.Branch r name idConstr pattern body'
             where lenPat  = length pattern
                   lenArgs = length targs
         Just _ -> throw $ PatternNotConstructor name
         Nothing -> throw $ UndefinedName r name


scopeApp :: (MonadTCM tcm) => A.Expr -> [A.Expr] -> tcm A.Expr
scopeApp e@(A.Ident r x) args =
  do xs <- getLocalNames
     case findIndex (==x) xs of
       Just n -> return $ A.buildApp (A.Bound r x n) args
       Nothing ->
         do g <- lookupGlobal x
            case g of
              Just (I.Inductive {}) -> return $ A.buildApp (A.Ind r Empty x) args
              Just (I.Constructor i idConstr parsTp argsTp _) ->
                  if expLen /= givenLen
                  then wrongArg cRange x expLen givenLen
                  else return $ A.Constr cRange x (i,idConstr) cpars cargs
                where
                  parLen = length parsTp
                  argLen = length argsTp
                  givenLen = length args
                  expLen = parLen + argLen
                  (cpars, cargs) = splitAt parLen args
                  cRange = fuseRange r args
              Just _ -> return $ A.buildApp e args
              Nothing -> undefinedName r x
scopeApp e args = return $ A.buildApp e args


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
  scope (A.InductiveDef x ps e cs) =
      do ps' <- scope ps
         e'  <- fakeBinds (reverse ps) $ scope e
         cs' <- fakeBinds (reverse ps) $ fakeBinds x $ mapM scope cs
         checkIfDefined x
         return $ A.InductiveDef x ps' e' cs'

instance Scope A.Parameter where
  scope (A.Parameter r np e) = fmap (A.Parameter r np) (scope e)


instance Scope A.Constructor where
  scope (A.Constructor r x e idConstr) =
    do e' <- scope e
       checkIfDefined x
       return (A.Constructor r x e' idConstr)
