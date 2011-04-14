{-# LANGUAGE PackageImports, FlexibleContexts, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances, DeriveDataTypeable,
  TypeSynonymInstances
 #-}
{-# LANGUAGE CPP #-}

-- Scope checking of Declaration and Expr
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
import Syntax.Name
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

  scope = return -- REMOVE THIS!!

-- We don't need the real type of the binds for scope checking, just the names
fakeBinds :: [Name] -> [I.Bind]
fakeBinds = map $ flip I.Bind I.tProp

instance Scope A.Bind where
  scope (A.Bind r xs e) = fmap (A.Bind r xs) (scope e)
  scope (A.NoBind e) = fmap A.NoBind (scope e)


instance (Scope a, HasNames a) => Scope [a] where
  scope [] = return []
  scope (x:xs) = do s <- scope x
                    ss <- local (fakeBinds (getNames x)++) $ scope xs
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
       e' <- local (newBinds++) $ scope e
       return $ A.Pi r bs' e'
         where newBinds = fakeBinds $ reverse $ concatMap getNames bs
  scope (A.Lam r bs e) =
    do bs' <- scope bs
       e' <- local (newBinds++) $ scope e
       l <- ask
       return $ A.Lam r bs' e'
         where newBinds = fakeBinds $ reverse $ concatMap getNames bs
  scope t@(A.App r e1 e2) =
    scopeApp f (as ++ [(r,e2)])
      where (f, as) = getFuncArgs e1
            getFuncArgs (A.App r e1 e2) =
              (f, as ++ [(r,e2)])
                where (f, as) = getFuncArgs e1
            getFuncArgs e = (e, [])
  scope t@(A.Var r x) =
    do l <- ask
       case findIndex (==x) (map getName l) of
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

scopeApp :: (MonadTCM tcm) => A.Expr -> [(Range, A.Expr)] -> tcm A.Expr
scopeApp e@(A.Var r x) args =
  do l <- ask
     case findIndex (==x) (map getName l) of
       Just n -> return $ mkFunc (A.Bound r x n) args
       Nothing ->
         do g <- lookupGlobal x
            case g of
              Just i@(I.Inductive {}) -> return $ mkFunc (A.Ind r x) args
              -- Just (ConstrDef i id pars args _) -> return $ mkConstr (wrongArg p x) x i (cxtSize params) (cxtSize args)
              Just _ -> return $ mkFunc e args
              Nothing -> undefinedName r x
scopeApp e args = return $ mkFunc e args

mkFunc :: A.Expr -> [(Range, A.Expr)] -> A.Expr
mkFunc func args = foldr (\(r,e1) y -> A.App r y e1) func args
-- mkConstr err x i m n = (\p a -> do when (length a/=m+n) $ err (length a) (m+n)
--                                    let a' = reverse $ take (m+n) a
--                                        params = map snd $ take m a'
--                                        args = map snd $ drop m a'
--                                    return $ Constr p x i params args, [])

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
    scope t@(A.Import _) = return t
    scope (A.Inductive r x ps e cs) =
      do ps' <- scope ps
         e' <- local (bindPars++) $ scope e
         cs' <- local (bindParsInd++) $ scope cs
         return $ A.Inductive r x ps' e' cs'
           where bindPars = fakeBinds $ concatMap getNames ps
                 bindParsInd = bindPars ++ fakeBinds [x]


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