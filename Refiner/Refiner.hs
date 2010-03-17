{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts
  #-}
{-# LANGUAGE CPP #-}

module Refiner.Refiner where

#include "../undefined.h"
import Utils.Impossible

import Utils.Fresh

import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Writer
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Syntax.Bind
import Syntax.Internal hiding (lift)
import qualified Syntax.Internal as I
import qualified Syntax.Abstract as A
import Syntax.Global
import Refiner.Unify
import Refiner.RM
import Environment


-- checkSort :: (Monad m) => A.Sort -> m Term
checkSort A.Star = return (TSort Box, TSort Star, [])
checkSort A.Box = return (TSort Box, TSort Box, [])

-- isSort :: (MonadRM rm) => Term -> rm ()
isSort (TSort s) = return s
isSort t = refinerError $ RefinerError $ "is sort" -- ++ show t

-- checkProd :: (MonadRM rm) => Term -> Term -> rm Term
checkProd s1 Box = Box
checkProd s1 Star = Star
-- checkProd t1 t2 = typeError $ InvalidProductRule t1 t2

-- We assume that in the global environment, types are normalized

refine :: (MonadRM rm) => A.Expr -> Type -> rm ETerm
refine e t = do (e', _) <- check e (upcast t)
                return e'


refine_ :: (MonadRM rm) => A.Expr -> rm (EType, ETerm, Subst)
refine_ (A.EVar _ e) = refinerError $ RefinerError $ "evar" ++ show e
refine_ (A.Ann _ t u) = do (r, u', sigma1) <- refine_ u
                           isSort r
                           (t', sigma2) <- check t u'
                           return (apply sigma1 u', apply sigma2 t', sigma1 <+> sigma2)
refine_ (A.TSort _ s) = checkSort s
refine_ (A.Pi _ b t2) = do (r1, t1', sigma1) <- refine_ (expr b)
                           s1 <- isSort r1
                           (r2, t2', sigma2) <- local (fmap (const t1') b:) $ refine_ t2
                           s2 <- isSort r2
                           return (TSort $ checkProd s1 s2,
                                   Pi (fmap (const (apply sigma2 t1')) b) t2',
                                   sigma1 <+> sigma2)
refine_ (A.Bound _ n) = do l <- ask
                           return (I.lift (n+1) 0 $ expr (l !! n), Bound n, [])
refine_ (A.Var _ x) = do t <- lookupGlobal x
                         case t of
                           Def t _ -> return (upcast t, Free x, [])
                           Axiom t -> return (upcast t, Free x, [])
refine_ (A.Lam _ b u) = do (r1, t', sigma1) <- refine_ (expr b)
                           isSort r1
                           (r2, u', sigma2) <- local (fmap (const t') b:) $ refine_ u
                           -- s <- refine_ g l (Pi t r2)
                           -- isSort s
                           return (Pi (fmap (const t') b) r2,
                                   Lam (fmap (const (apply sigma2 t')) b) u',
                                   sigma1 <+> sigma2)
refine_ (A.App _ t1 t2) = do (r1, t1', sigma1) <- refine_ t1
                             w1 <- whnf r1
                             case w1 of
                               Pi u1 u2 -> do (t2', sigma2) <- local (map $ fmap $ apply sigma1) $ check t2 (expr u1)
                                              let t11 = apply sigma2 t1'
                                                  rr = apply sigma2 (subst t2' u2)
                                              mapGoal (apply sigma2)
                                              return (rr,
                                                      App t11 t2',
                                                      sigma1 <+> sigma2)
                               otherwise -> refinerError $ RefinerError $ "not function " -- ++ show t1'

check :: (MonadRM rm) => A.Expr -> EType -> rm (ETerm, Subst)
check (A.EVar _ _) u = do i <- fresh
                          l <- ask
                          addGoal i $ Goal l u
                          return (Meta i 0 (length l), [])
check t@(A.Lam _ b t2) u = do (r1, _, _) <- refine_ (reify u) -- not nice
                              (t1', sigmat) <- check (expr b) r1
                              w1 <- whnf u
                              case w1 of
                                Pi u1 u2 -> do sigma1 <- unify t1' (expr u1)
                                               (t2', sigma2) <- local (fmap (const t1') b:) $ check t2 u2
                                               let ss = sigmat <+> sigma1 <+> sigma2
                                               return (Lam (fmap (const (apply ss t1')) b) (apply ss t2'), ss)
                                otherwise -> refinerError $ RefinerError $ "check lam " -- ++ show t
check t u = do l <- ask
               (u', t', sigma') <- refine_ t
               sigma <- unify u u'
               let ss = sigma' <+> sigma
               mapM_ removeGoal (domain ss)
               mapGoal (apply ss)
               return (apply ss t', ss)

