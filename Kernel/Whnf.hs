{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances,
  CPP #-}

module Kernel.Whnf where

#include "../undefined.h"
import Utils.Impossible

import Syntax.Bind
import Syntax.Internal
import Syntax.Global
import Environment
import Kernel.TCM

whnf :: (MonadTCM tcm) => Term -> tcm Term
whnf t@(App t1 t2) = do u1 <- whnf t1
                        case u1 of
                          Lam _ u -> whnf $ subst t2 u
                          u       -> return $ App u t2
whnf t@(Free x) = do d <- lookupGlobal x
                     case d of
                       Def _ u -> return u
                       Axiom _ -> return t
                       IndDef _ _ _ _ -> return t
whnf t = return t

class NormalForm a where
    normalForm :: (MonadTCM tcm) => a -> tcm a

instance NormalForm BindT where
    normalForm (NoBind t) = do n <- normalForm t
                               return $ NoBind n
    normalForm (Bind x t) = do n <- normalForm t
                               return $ Bind x n

instance NormalForm Term where
    normalForm t@(TSort _) = return t
    normalForm (Pi b t2) = do u1 <- normalForm b
                              u2 <- normalForm t2
                              return $ Pi u1 u2
    normalForm t@(Bound _) = return t
    normalForm t@(Free x) = do u <- lookupGlobal x
                               case u of
                                 Def _ t' -> normalForm  t'
                                 Axiom _ -> return t
    normalForm (Lam b u) = do t1 <- normalForm b
                              u1 <- normalForm u
                              return $ Lam b u1
    normalForm (App t1 t2) = do u1 <- normalForm t1
                                case u1 of
                                  Lam _ v -> normalForm $ subst t2 v
                                  App _ _ -> do u2 <- normalForm t2
                                                return $ App u1 u2
                                  Bound _ -> do u2 <- normalForm t2
                                                return $ App u1 u2
                                  Free _  -> do u2 <- normalForm t2
                                                return $ App u1 u2
                                  otherwise -> __IMPOSSIBLE__

