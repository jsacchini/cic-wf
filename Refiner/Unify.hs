{-# LANGUAGE PackageImports, MultiParamTypeClasses, FlexibleInstances, 
  TypeSynonymInstances #-}
{-# LANGUAGE CPP #-}

module Refiner.Unify where

#include "../undefined.h"
import Utils.Impossible

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.State
import Syntax.Internal
import Syntax.ETag
import Environment
import Refiner.RM

type Subst = [(MetaId, Term EVAR)]

(<+>) :: Subst -> Subst -> Subst
(<+>) = (++)

domain :: Subst -> [MetaId]
domain = map fst

class Apply a where
    apply :: Subst -> a -> a

instance Apply (Term EVAR) where
    -- apply :: Subst -> Term EVAR -> Term EVAR
    apply [] t = t
    apply ((i, t1): s) t = apply s $ substMeta i t1 t

instance Apply (NamedCxt EVAR) where
    apply s = map (\(x,t) -> (x,apply s t))

whnf :: (MonadRM rm) => Term a -> rm (Term a)
whnf t@(App t1 t2) = do u1 <- whnf t1
                        case u1 of
                          Lam x _ u -> whnf $ subst t2 u
                          u -> return $ App u t2
whnf t@(Free x) = do d <- lookupGlobal x
                     case d of
                       Def _ u -> return $ cast u
                       Axiom _ -> return t
whnf t = return t


-- remove :: Subst -> [(MetaId, a, b)] -> [(MetaId, a, b)]
-- remove :: Subst -> [(MetaId, ([Type], Type))] -> [(MetaId, ([Type], Type))]
remove s = (map (\(x,t) -> (x+300,([],t))) s++) . ((100, ([],TSort Box)):)-- filter $ flip notElem (map fst s) . fst 

unify :: (MonadRM rm) => Term EVAR -> Term EVAR -> rm Subst
unify t1 t2 = do w1 <- whnf t1
                 w2 <- whnf t2
                 case (w1, w2) of
                   (Meta i _ _, _) -> return [(i, w2)]
                   (_, Meta i _ _) -> return [(i, w2)]
                   (Free x, Free y) -> do when (x /= y) $ refinerError RefinerError
                                          return []
                   (Bound m, Bound n) -> do when (m /= n) $ refinerError RefinerError
                                            return []
                   (TSort s1, TSort s2) -> do when (s1 /= s2) $ refinerError RefinerError
                                              return []
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


