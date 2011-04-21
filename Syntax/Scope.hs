{-# LANGUAGE PackageImports, FlexibleContexts, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances, DeriveDataTypeable,
  TypeSynonymInstances
 #-}
{-# LANGUAGE CPP #-}

-- | Scope checking of Declaration and Expr
-- It replaces
-- * Var x           --> Bound n  for bound variables
-- * Var i           --> Ind i    for inductive types
-- * App (Var c ...) --> Constr c j ...   for constructors, checking they are
--                                        fully applied


module Syntax.Scope -- (scope,
                    --  ScopeError(..),
                    --  ScopeMonad,
                    --  Scope)
       where

#include "../undefined.h"
import Utils.Impossible

import "mtl" Control.Monad.Reader
import Control.Exception

import Data.List
import Data.Typeable

import qualified Syntax.Abstract as A
import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Utils.Misc

import Kernel.TCM


wrongArg :: (MonadTCM tcm) => Range -> Name -> Int -> Int -> tcm a
wrongArg r x m n = typeError $ WrongNumberOfArguments r x m n

undefinedName :: (MonadTCM tcm) => Range -> Name -> tcm a
undefinedName r x = typeError $ UndefinedName r x

constrNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
constrNotApplied r x = typeError $ ConstructorNotApplied r x

-- We reuse the type-checking monad for scope checking
class Scope a where
  scope :: MonadTCM m => a -> m a

  scope = error "implement Scope checker" -- REMOVE THIS!!

-- We don't need the real type of the binds for scope checking, just the names
fakeBinds :: (MonadTCM tcm, HasNames a) => a -> tcm b -> tcm b
fakeBinds b m = local (map (flip I.Bind I.tProp) (getNames b)++) m

fakeBindsIn :: (MonadTCM tcm) => [Name] -> tcm a -> tcm a
fakeBindsIn xs = local $ (map (flip I.Bind I.tProp) xs++)

instance Scope A.Bind where
  scope (A.Bind r xs e) = fmap (A.Bind r xs) (scope e)
  -- scope (A.NoBind e) = fmap A.NoBind (scope e)


instance (Scope a, HasNames a) => Scope [a] where
  scope [] = return []
  scope (x:xs) = do s <- scope x
                    ss <- fakeBindsIn (reverse (getNames x)) $ scope xs
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
       e' <- fakeBindsIn newBinds $ scope e
       return $ A.Pi r bs' e'
         where newBinds = reverse $ concatMap A.bindNames bs
  scope (A.Arrow r e1 e2) =
    do e1' <- scope e1
       e2' <- fakeBinds noName $ scope e2
       return $ A.Arrow r e1' e2'
  scope (A.Lam r bs e) =
    do bs' <- scope bs
       e' <- fakeBindsIn newBinds $ scope e
       l <- ask
       return $ A.Lam r bs' e'
         where newBinds = reverse $ concatMap A.bindNames bs
  scope t@(A.App r e1 e2) =
    do args' <- mapM scope args
       scopeApp func args'
      where
        (func, args) = A.destroyApp t
  scope t@(A.Var r x) =
    do xs <- getLocalNames
       case findIndex (==x) xs of
         Just n -> return $ A.Bound r x n
         Nothing ->
           do g <- lookupGlobal x
              case g of
                Just i@(I.Inductive {}) -> return $ A.Ind r x
                Just c@(I.Constructor {}) -> constrNotApplied r x
                Just _ -> return t
                Nothing -> undefinedName r x

-- scope (Fix p n f args ret body) = do sargs <- scope args
    --                                      sret <- local (map bind args++) (scope ret)
    --                                      unless (n > 0 && n <= length args) $ scopeError $ WrongFixNumber p f n
    --                                      sbody <- local (f:) (scope body)
    --                                      return $ Fix p n f sargs sret sbody
    -- scope (Match p (MkMatch arg aname iname ret bs)) = do sarg <- scope arg
    --                                                       checkArgNum iname
    --                                                       sret <- local (names++) (scope ret)
    --                                                       sbs <- mapM scope bs
    --                                                       return $ Match p (MkMatch sarg aname iname sret (map updBranch (zip (from 0) sbs)))
    --     where names = maybe [] return aname ++ maybe [] snd iname
    --           checkArgNum (Just (n,as)) = do checkInd p n
    --                                          nargs <- argsInd n
    --                                          when (length as /= nargs) $ wrongArg p n (length as) nargs
    --           checkArgNum Nothing = return ()
    --           checkInd p n = mUnless (definedName n) (scopeError $ UndefinedName p n) >>
    --                          mUnless (isInd n) (scopeError $ NotInductive n)
    --           updBranch (i, MkBranch c _ a b) = MkBranch c i a b
    --           from n = n : from (n+1)
  scope t@(A.Bound _ _ _) = __IMPOSSIBLE__
  scope t@(A.Ind _ _) = __IMPOSSIBLE__

-- instance Scope Branch where
--     scope (MkBranch cname i args body) = do sbody <- local (args++) (scope body)
--                                             return $ MkBranch cname i args sbody

scopeApp :: (MonadTCM tcm) => A.Expr -> [A.Expr] -> tcm A.Expr
scopeApp e@(A.Var r x) args =
  do xs <- getLocalNames
     case findIndex (==x) xs of
       Just n -> return $ A.buildApp (A.Bound r x n) args
       Nothing ->
         do g <- lookupGlobal x
            case g of
              Just i@(I.Inductive {}) -> return $ A.buildApp (A.Ind r x) args
              Just (I.Constructor i id parsTp argsTp _) ->
                  if expLen /= givenLen
                  then wrongArg cRange x expLen givenLen
                  else return $ A.Constr cRange x (i,id) cpars cargs
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
         return $ A.Definition r x t' u'
    scope (A.Assumption r x t) =
      do t' <- scope t
         return $ A.Assumption r x t'
    -- scope (A.Inductive r x ps e cs) =
    --   do ps' <- scope ps
    --      e'  <- fakeBinds (reverse ps) $ scope e
    --      cs' <- fakeBinds (reverse ps) $ fakeBinds x $ mapM scope cs
    --      return $ A.Inductive r x ps' e' cs'


instance Scope A.Parameter where
  scope (A.Parameter r np e) = fmap (A.Parameter r np) (scope e)


instance Scope A.Constructor where
  scope (A.Constructor r x e id) =
    do e' <- scope e
       return (A.Constructor r x e' id)

{-
instance Scope IndExpr where
    scope (MkInd x params arg cs) = do sp <- scope params
                                       let indbinds = reverse $ x : map bind params
                                       sa <- local (indbinds++) (scope arg)
                                       scs <- mapM (local (indbinds++) . scope) cs
                                       return $ MkInd x sp sa scs

instance Scope ConstrExpr where
    scope (MkConstrExpr x t) = scope t >>= return . MkConstrExpr x

appScope :: (ScopeMonad m) => Expr -> m (Pos -> [(Pos, Expr)] -> m Expr, [(Pos, Expr)])
appScope (App p e1 e2) = do (f, as) <- appScope e1
                            s2 <- scope e2
                            return (f, (p,s2):as)
appScope (Var p x) =
    do l <- ask
       case findIndex (==x) l of
         Just n -> return $ mkFun (Bound p n)
         Nothing -> do g <- lookupName x
                       case g of
                         Just (IndDef params args _ _) -> return $ mkFun (Ind p x)
                         Just (ConstrDef i params _ _ args _) -> return $ mkConstr (wrongArg p x) x i (cxtSize params) (cxtSize args)
                         Just _ -> return $ mkFun (Var p x)
                         Nothing -> scopeError $ UndefinedName p x
appScope e = return $ mkFun e

-}