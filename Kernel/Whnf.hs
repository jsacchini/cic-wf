{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, CPP #-}

module Kernel.Whnf where

#include "../undefined.h"
import Utils.Impossible

import Syntax.Internal
import Environment
import Kernel.TCM

whnf :: (MonadTCM tcm) => Term a -> tcm (Term a)
whnf t@(App t1 t2) = do u1 <- whnf t1
                        case u1 of
                          Lam x _ u -> whnf $ subst t2 u
                          u         -> return $ App u t2
whnf t@(Free x) = do d <- lookupGlobal x
                     case d of
                       Def _ u -> return $ cast u
                       Axiom _ -> return t
whnf t = return t


normalForm :: (MonadTCM tcm) => Term a -> tcm (Term a) 
normalForm t@(TSort _) = return t
normalForm (Pi x t1 t2) = do u1 <- normalForm t1
                             u2 <- normalForm t2
                             return $ Pi x u1 u2
normalForm t@(Bound _) = return t
normalForm t@(Free x) = do u <- lookupGlobal x
                           case u of
                             Def _ t' -> normalForm $ cast t'
                             Axiom _ -> return $ t
normalForm (Lam x t u) = do t1 <- normalForm t
                            u1 <- normalForm u
                            return $ Lam x t1 u1
normalForm (App t1 t2) = do u1 <- normalForm t1
                            case u1 of
                              Lam _ t v -> normalForm $ subst t2 v
                              App _ _ -> do u2 <- normalForm t2
                                            return $ App u1 u2
                              Bound _ -> do u2 <- normalForm t2
                                            return $ App u1 u2
                              Free _  -> do u2 <- normalForm t2
                                            return $ App u1 u2
                              Meta _ _ _ -> do u2 <- normalForm t2
                                               return $ App u1 u2
                              otherwise -> __IMPOSSIBLE__
normalForm t@(Meta _ _ _) = return t
