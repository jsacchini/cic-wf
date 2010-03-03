{-# LANGUAGE PackageImports, MultiParamTypeClasses, FlexibleInstances, 
  TypeSynonymInstances #-}
{-# LANGUAGE CPP #-}

module Refiner.Unify where

#include "../undefined.h"
import Utils.Impossible

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.State

import Data.Foldable hiding (notElem)
import Control.Arrow (second)

import Environment

import Syntax.Bind
import Syntax.Internal
import Syntax.Global
import Refiner.RM

type Subst = [(MetaId, ETerm)]

(<+>) :: Subst -> Subst -> Subst
(<+>) = (++)

domain :: Subst -> [MetaId]
domain = map fst

class Apply a where
    apply :: Subst -> a -> a

instance Apply ETerm where
    apply [] t = t
    apply ((i, t1): s) t = apply s $ substMeta i t1 t

instance Apply ENamedCxt where
    apply s = map (fmap $ apply s)

instance Apply Goal where
    apply s (Goal e t) = Goal (apply s e) (apply s t)

whnf :: (MonadRM rm) => ETerm -> rm ETerm
whnf t@(App t1 t2) = do u1 <- whnf t1
                        case u1 of
                          Lam _ u -> whnf $ subst t2 u
                          u -> return $ App u t2
whnf t@(Free x) = do d <- lookupGlobal x
                     case d of
                       Def _ u -> return $ upcast u
                       Axiom _ -> return t
whnf t = return t


remove s = filter $ flip notElem (map fst s) . fst 

unify :: (MonadRM rm) => ETerm -> ETerm -> rm Subst
unify t1 t2 = do w1 <- whnf t1
                 w2 <- whnf t2
                 case (w1, w2) of
                   (Meta i _ _, _) -> return [(i, w2)] -- missing occur check
                   (_, Meta i _ _) -> return [(i, w1)] -- missing occur check
                   (Free x, Free y) -> do when (x /= y) $ refinerError $ RefinerError $ "unify free" -- ++ show w1 ++ " " ++ show w2
                                          return []
                   (Bound m, Bound n) -> do when (m /= n) $ refinerError $ RefinerError $ "unify bound" -- ++ show w1 ++ " " ++ show w2
                                            return []
                   (TSort s1, TSort s2) -> do when (s1 /= s2) $ refinerError $ RefinerError $ "unify sort" -- ++ show w1 ++ " " ++ show w2
                                              return []
                   (Pi u1 u2, Pi v1 v2) -> do sigma1 <- unify (expr u1) (expr v1)
                                              sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                              return $ sigma1 <+> sigma2
                   (Lam u1 u2, Lam v1 v2) -> do sigma1 <- unify (expr u1) (expr v1)
                                                sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                                return $ sigma1 <+> sigma2
                   (App u1 u2, App v1 v2) -> do sigma1 <- unify u1 v1
                                                sigma2 <- unify (apply sigma1 u2) (apply sigma1 v2)
                                                return $ sigma1 <+> sigma2
                   (_, _) -> refinerError $ RefinerError $ "unify " -- ++ show w1 ++ " " ++ show w2


