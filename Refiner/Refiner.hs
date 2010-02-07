{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts
  #-}
{-# LANGUAGE CPP #-}

module Refiner.Refiner where

#include "../undefined.h"
import Impossible

import Utils.Fresh

import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Writer
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Refiner.Internal hiding (lift)
import qualified Refiner.Internal as I
import qualified Abstract as A
import Refiner.Conversion
import Refiner.RM
import Refiner.Environment


-- checkSort :: (Monad m) => A.Sort -> m Term
checkSort A.Star = return (TSort Box, TSort Star, [])
checkSort A.Box = return (TSort Box, TSort Box, [])

-- isSort :: (MonadRM rm) => Term -> rm ()
isSort (TSort _) = return ()
isSort t = refinerError RefinerError

-- checkProd :: (MonadRM rm) => Term -> Term -> rm Term
checkProd (TSort s1) (TSort Box) = TSort Box
checkProd (TSort s1) (TSort Star) = TSort Star
-- checkProd t1 t2 = typeError $ InvalidProductRule t1 t2

-- We assume that in the global environment, types are normalized

refine :: (MonadRM s rm) => A.Expr -> rm (Type, Term, Subst)
refine (A.Meta _ _) = refinerError RefinerError
refine (A.Ann _ t u) = do (r, u', sigma1) <- refine u
                          isSort r
                          (t', sigma2) <- check t u'
                          return (apply sigma1 u', apply sigma2 t', sigma1 <+> sigma2)
refine (A.TSort _ s) = checkSort s
refine (A.Pi _ x t1 t2) = do (r1, t1', sigma1) <- refine t1
                             isSort r1
                             (r2, t2', sigma2) <- local (t1':) $ refine t2
                             isSort r2
                             return (checkProd r1 r2,
                                     Pi x (apply sigma2 t1') t2',
                                     sigma1 <+> sigma2)
refine (A.Bound _ n) = do l <- ask
                          return $ (I.lift (n+1) 0 $ l !! n, Bound n, [])
refine (A.Free _ x) = do t <- lookupGE x 
                         case t of
                           Def t _ -> return (t, Free x, [])
                           Axiom t -> return (t, Free x, [])
refine (A.Lam _ x t u) = do (r1, t', sigma1) <- refine t
                            isSort r1
                            (r2, u', sigma2) <- local (t':) $ refine u
                            -- s <- refine g l (Pi t r2)
                            -- isSort s
                            return (Pi x t' r2,
                                    Lam x (apply sigma2 t') u',
                                    sigma1 <+> sigma2)
refine (A.App _ t1 t2) = do (r1, t1', sigma1) <- refine t1
                            w1 <- whnf r1
                            case w1 of
                              Pi _ u1 u2 -> do (t2', sigma2) <- local (map (apply sigma1)) $ check t2 u1
                                               let t11 = apply sigma2 t1'
                                                   rr = apply sigma2 (subst t2' u2)
                                               return $ (rr,
                                                         App t11 t2',
                                                         sigma1 <+> sigma2)
                              otherwise -> refinerError RefinerError

-- check :: (MonadRM rm) => A.Expr -> Term -> rm ()
check :: (MonadRM s rm) => A.Expr -> Term -> rm (Term, Subst)
check (A.Meta _ _) u = do i <- fresh
                          l <- ask
                          addGoal i $ Goal l u
                          return $ (Meta i 0 (length l), [])
check t u = do (u', t', sigma') <- refine t
               sigma <- unify u u'
               let ss = sigma' <+> sigma
               mapM_ removeGoal (domain ss)
               return (apply sigma t', ss)
               

-- lcheck :: (MonadRM rm) => [A.Expr] -> [Term] -> rm ()
lcheck [] [] = return ()
lcheck (t:ts) (u:us) = do check t u
	                  lcheck ts (mapsubst 0 (interp t) us)
