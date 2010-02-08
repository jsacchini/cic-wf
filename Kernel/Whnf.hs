{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, CPP #-}

module Kernel.Whnf where

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
