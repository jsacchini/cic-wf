{-# LANGUAGE PackageImports, MultiParamTypeClasses, FlexibleInstances, CPP #-}

module Refiner.Conversion where

#include "../undefined.h"
import Impossible

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.State
import Refiner.Internal
import Refiner.Environment
import Refiner.RM

type Subst = [(MetaId, Term)]

(<+>) :: Subst -> Subst -> Subst
(<+>) = (++)

domain :: Subst -> [MetaId]
domain = map fst

apply :: Subst -> Term -> Term
apply [] t = t
apply ((i, t1): s) t = apply s $ substMeta i t1 t

whnf :: (MonadGE m) => Term -> m Term
whnf t@(App t1 t2) = do u1 <- whnf t1
                        case u1 of
                          Lam x _ u -> whnf $ subst t2 u
                          u -> return $ App u t2
whnf t@(Free x) = do d <- lookupGE x
                     case d of
                       Def _ u -> return u
                       Axiom _ -> return t
whnf t = return t


-- remove :: Subst -> [(MetaId, a, b)] -> [(MetaId, a, b)]
remove :: Subst -> [(MetaId, ([Type], Type))] -> [(MetaId, ([Type], Type))]
remove s = (map (\(x,t) -> (x+300,([],t))) s++) . ((100, ([],TSort Box)):)-- filter $ flip notElem (map fst s) . fst 

-- unify :: (MonadTCM tcm) => Term -> Term -> tcm ()
unify t1 t2 = do w1 <- whnf t1
                 w2 <- whnf t2
                 case (w1, w2) of
                   (Meta i _ _, _ )-> return [(i, w2)]
                   (_, Meta i _ _) -> return [(i, w2)]
                   (Pi _ u1 u2, Pi _ v1 v2) -> do sigma1 <- unify u1 v1
                                                  sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                                  return $ sigma1 <+> sigma2
                   (Lam _ u1 u2, Lam _ v1 v2) -> do sigma1 <- unify u1 v1
                                                    sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                                    return $ sigma1 <+> sigma2
                   (App u1 u2, App v1 v2) -> do sigma1 <- unify u1 v1
                                                sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                                return $ sigma1 <+> sigma2
                   (_, _) -> refinerError RefinerError


