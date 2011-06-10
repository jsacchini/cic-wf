{-# LANGUAGE TypeSynonymInstances #-}

module Unification where

import Data.List

import Syntax.Internal

import Kernel.TCM
import Kernel.Whnf
import Kernel.Conversion

import Utils.Misc

type Equation = (Term, Term) -- an equation is just a pair of terms

instance SubstTerm Equation where
  substN k t (t1, t2) = (substN k t t1, substN k t t2)

-- unify a set of equation with respect to a set of bound vars
unify :: (MonadTCM tcm) => [Equation] -> [Int] -> tcm (Substitution, [Int])
unify [] ks = return ([], ks)
unify ((t1,t2):es) ks = do w1 <- whnf t1
                           w2 <- whnf t2
                           (sg1, js) <- unifyEq (w1,w2) ks
                           (sg2, ls) <- unify (map (applySubst sg1) es) (ks \\ js)
                           return (sg1 ++ sg2, ls)

-- unify just one equation, we assume that the terms of the equation
-- are in whnf
unifyEq :: (MonadTCM tcm) => Equation -> [Int] -> tcm (Substitution, [Int])
unifyEq (Bound k, t2) js | k `elem` js = return ([(k, t2)], js \\ [k])
                         | otherwise   = do unlessM (conversion (Bound k) t2) $ typeError NotUnifiable
                                            return ([], js)
unifyEq (t1, Bound k) js = unifyEq (Bound k, t1) js
-- TODO: check that Constr are not in sort Prop
unifyEq (Constr x1 cid1 ps1 as1, Constr x2 cid2 ps2 as2) js =
  if x1 == x2
  then unify (zip as1 as2) js
  else typeError NotUnifiable
unifyEq (t1, t2) js = do unlessM (conversion t1 t2) $ typeError NotUnifiable
                         return ([], js)
