{-# LANGUAGE PackageImports, FlexibleContexts, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances, DeriveDataTypeable,
  TypeSynonymInstances
 #-}
{-# LANGUAGE CPP #-}

module Syntax.Scope (scope,
                     ScopeError(..),
                     ScopeMonad,
                     Scope) where

#include "../undefined.h"
import Utils.Impossible

import "mtl" Control.Monad.Reader
import qualified Control.Exception as E

import Data.List
import Data.Typeable

import Environment
import Syntax.Abstract
import Syntax.Bind
import Syntax.Name
import Syntax.Global
import Syntax.Position
import Kernel.TCM
import Utils.Misc

data ScopeError = WrongNumberOfArguments Position Name Int Int
                | WrongFixNumber Position Name Int
                | UndefinedName Position Name
                | NotInductive Name
                deriving(Show,Typeable)

instance E.Exception ScopeError

scopeError :: (MonadIO m) => ScopeError -> m a
scopeError = liftIO . E.throwIO

wrongArg p x m n = scopeError $ WrongNumberOfArguments p x m n

class (Monad m,
       MonadIO m,
       MonadReader [Name] m,
       LookupName Global m) => ScopeMonad m where

class Scope a where
    scope :: (ScopeMonad m) => a -> m a

instance Scope BindE where
    scope (Bind x e) = scope e >>= return . Bind x
    scope (NoBind e) = scope e >>= return . NoBind

instance Scope Expr where
    scope (Ann p e1 e2) = do s1 <- scope e1
                             s2 <- scope e2
                             return $ Ann p s1 s2
    scope (Pi p b e2) = do s1 <- scope b
                           s2 <- local (bind b:) $ scope e2
                           return $ Pi p s1 s2
    scope (Lam p b e2) = do s1 <- scope b
                            s2 <- local (bind b:) $ scope e2
                            return $ Lam p s1 s2
    scope t@(App p e1 e2) = do (f, as) <- appScope t
                               f p as
    scope t@(Var p x) = do (f, _) <- appScope t
                           f p []
    scope (Fix p n f args ret body) = do sargs <- scope args
                                         sret <- local (map bind args++) (scope ret)
                                         unless (n > 0 && n <= length args) $ scopeError $ WrongFixNumber p f n
                                         sbody <- local (f:) (scope body)
                                         return $ Fix p n f sargs sret sbody
    scope (Match p (MkMatch arg aname iname ret bs)) = do sarg <- scope arg
                                                          checkArgNum iname
                                                          sret <- local (names++) (scope ret)
                                                          sbs <- mapM scope bs
                                                          return $ Match p (MkMatch sarg aname iname sret (map updBranch (zip (from 0) sbs)))
        where names = maybe [] return aname ++ maybe [] snd iname
              checkArgNum (Just (n,as)) = do checkInd p n
                                             nargs <- argsInd n
                                             when (length as /= nargs) $ wrongArg p n (length as) nargs
              checkArgNum Nothing = return ()
              checkInd p n = mUnless (definedName n) (scopeError $ UndefinedName p n) >>
                             mUnless (isInd n) (scopeError $ NotInductive n)
              updBranch (i, MkBranch c _ a b) = MkBranch c i a b
              from n = n : from (n+1)
    scope t@(TSort _ _) = return t
    scope t@(EVar _ _) = return t
    scope t@(Bound _ _) = __IMPOSSIBLE__
    scope t@(Ind _ _ _) = __IMPOSSIBLE__

instance Scope Branch where
    scope (MkBranch cname i args body) = do sbody <- local (args++) (scope body)
                                            return $ MkBranch cname i args sbody

instance (Scope a) => Scope (Maybe a) where
    scope (Just x) = do s <- scope x
                        return $ Just s
    scope Nothing = return Nothing

instance (Scope a, BindClass a) => Scope [a] where
    scope [] = return []
    scope (x:xs) = do s <- scope x
                      ss <- local (bind x:) (scope xs)
                      return (s:ss)

instance (Scope a, Scope b, BindClass a) => Scope (a,b) where
    scope (x,y) = do sx <- scope x
                     sy <- local (bind x:) (scope y)
                     return (sx,sy)

instance Scope Command where
    scope (Definition x t u) = do st <- scope t
                                  su <- scope u
                                  return $ Definition x st su
    scope (AxiomCommand x t) = do st <- scope t
                                  return $ AxiomCommand x st
    scope t@(Load _) = return t
    scope t@(Inductive i) = return t -- TODO!

appScope (App p e1 e2) = do (f, as) <- appScope e1
                            s2 <- scope e2
                            return (f, (p,s2):as)
appScope (Var p x) =
    do l <- ask
       case findIndex (==x) l of
         Just n -> return $ mkFun (Bound p n)
         Nothing -> do g <- lookupName x
                       case g of
                         Just (IndDef params args _ _) -> return $ mkInd (wrongArg p x) x (length params + length args)
                         Just (ConstrDef i params _ _ args _) -> return $ mkConstr (wrongArg p x) i (length params) (length args)
                         Just _ -> return $ mkFun (Var p x)
                         Nothing -> scopeError $ UndefinedName p x
appScope e = return $ mkFun e

mkFun e = (\_ as -> return $ foldr (\(p,e1) r -> App p r e1) e as, [])
mkInd err x n = (\p a -> do when (length a/=n) $ err (length a) n
                            return $ Ind p x (map snd a), [])
mkConstr err i m n = (\p a -> do when (length a/=m+n) $ err (length a) (m+n)
                                 return $ Constr p i (map snd (take m a)) (map snd (drop m a)), [])
