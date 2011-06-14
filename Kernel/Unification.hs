{-# LANGUAGE TypeSynonymInstances #-}

module Kernel.Unification where

import Control.Monad
import Control.Monad.Reader hiding (lift)
import qualified Control.Monad.Reader as R (lift)
import Data.List

import Syntax.Internal as I
import Syntax.InternaltoAbstract

import Kernel.TCM
import Kernel.Whnf
import Kernel.Conversion
import Kernel.Permutation

import Utils.Maybe
import Utils.Misc

type Equation = (Term, Term) -- an equation is just a pair of terms

instance SubstTerm Equation where
  substN k t (t1, t2) = (substN k t t1, substN k t t2)

unifyPos :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm (Context, Permutation, [Int])
unifyPos ctx eqs ks = do r <- runMT $ unify ctx eqs ks
                         case r of
                           Just x -> return x
                           Nothing -> typeError NotUnifiable

unifyNeg :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm ()
unifyNeg ctx eqs ks = do r <- runMT $ unify ctx eqs ks
                         case r of
                           Just x -> typeError NotImpossibleBranch
                           Nothing -> return ()


unify :: (MonadTCM tcm) =>
         Context -> [Equation] -> [Int] -> MaybeT tcm (Context, Permutation, [Int])
unify ctx [] ks = return (ctx, idP (ctxLen ctx), ks)
unify ctx ((t1,t2):es) ks = do
  -- Normalize the equation
  -- traceTCM_ ["Unifying equation ", show ctx, "\neq  ", show t1, " === ", show t2, "\nfor ", show ks, "\nrest of eqs: ", show es]
  w1 <- R.lift $ pushCtx ctx $ whnf t1
  w2 <- R.lift $ pushCtx ctx $ whnf t2
  -- traceTCM_ ["Normalized equation: ", show w1, " === ", show w2, "\nfor ", show ks]
  (ctx1, p1, ks1) <- unifyEq ctx (w1,w2) ks
  -- traceTCM_ ["result unifyEq ", show ctx1, " left ", show ks1, "\n perm : ", show p1]
  -- traceTCM_ ["REST ", show ctx1, "\neq  ", show $ map (applyPerm p1) es, "\nfor ", show ks1]
  (ctx2, p2, ks2) <- unify ctx1 (map (applyPerm p1) es) (map (applyPerm p1) ks1)
  R.lift $ traceTCM_ ["Combining all\nstarting ", show ctx, "\n\nfrom: ", show (w1,w2), "\nctx: ", show ctx1, "\nperm: ", show p1, "\nleft: ", show ks1, "\n\nfrom ", show es, "\nctx: ", show ctx2, "\nleft ", show ks2, "\n perm : ", show p2] --, "\n combining perm: "] -- , show $ combineP p2 p1]
  return (ctx2, combineP p2 p1, (map (applyPerm (combineP p2 p1)) ks2))




-- unify just one equation, we assume that the terms of the equation
-- are in whnf
unifyEq :: (MonadTCM tcm) =>
           Context -> Equation -> [Int] -> MaybeT tcm (Context, Permutation, [Int])
unifyEq ctx (Bound k1, Bound k2) js
  | k1 `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k1 (Bound k2)
                      -- traceTCM_ ["applyDef left result ", show ctx', "\nperm ", show p]
                      return (ctx', p, js \\ [k1])
  | k2 `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k2 (Bound k1)
                      -- traceTCM_ ["applyDef right result ", show ctx', "\nperm ", show p]
                      return (ctx', p, js \\ [k2])
  | otherwise    = do unless (k1 == k2) $ R.lift $ typeError NotUnifiable
                      return (ctx, idP (ctxLen ctx), js)
unifyEq ctx (Bound k, t2) js
  | k `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k t2
                     -- traceTCM_ ["applyDef left result ", show ctx', "\nperm ", show p]
                     return (ctx', p, js \\ [k])
  | otherwise   = do (unlessM (R.lift $ conversion (Bound k) t2)) $ R.lift $ typeError NotUnifiable
                     return (empCtx, idP (ctxLen ctx), js)
unifyEq ctx (t1, Bound k) js = unifyEq ctx (Bound k, t1) js
-- TODO: check that Constr are not in sort Prop
unifyEq ctx (Constr x1 cid1 ps1 as1, Constr x2 cid2 ps2 as2) js =
  if x1 == x2
  then do -- traceTCM_ ["unifying constructor ", show x1, "\nnew equations: ", show (zip as1 as2)]
          unify ctx (zip as1 as2) js
  else fail "Negative sucess"
unifyEq ctx (t1, t2) js =
  do unlessM (R.lift $ conversion t1 t2) $ R.lift $ typeError NotUnifiable
     return (empCtx, idP (ctxLen ctx), js)




applyDef :: (MonadTCM tcm) =>
            Context -> Int -> Term -> tcm (Context, Permutation)
applyDef ctx k t =
  do -- traceTCM_ ["strengthen ", show ctx0, "\n with ", show t, "\nat ", show k]
     (cxa, cxb, p) <- strengthen ctx0 t
     -- traceTCM_ ["obtained strengthen\nbefore: ", show cxa, "\nafter ", show cxb, "\nperm: ", show p]
     let cxa' = lift (-1) 1 cxa
         cxbP = insertP 0 (idP (ctxLen cxa))
         cxb' = applyPerm cxbP cxb
         p'   = insertP (ctxLen cxb) p ++> ctxLen ctx1
         t'   = lift (-(ctxLen cxb + 1)) 0 (applyPerm p' t)
         u'   = lift (ctxLen cxa) 0 u
     -- traceTCM_ ["applyinf def\nbefore: ", show cxa', {-"\nafter: ", show cxb',-} "\ndef: ", show (applyPerm p' t), " -> ", show (LocalDef x t' u'), "\nperm: ", show p']
     return (ctx1 +: cxa' +: (LocalDef x t' u' <| cxb'), p')
  where (ctx1, ExtendCtx (Bind x u) ctx0) = ctxSplitAt (ctxLen ctx - k - 1) ctx
        strengthen :: MonadTCM tcm => Context -> Term -> tcm (Context,Context,Permutation)
        strengthen EmptyCtx _ = return (empCtx, empCtx, Perm [])
        strengthen (ExtendCtx bind rest) t =
          do (beft, aft, p) <- strengthen rest t
             -- traceTCM_ ["in strengthen\nbefore: ", show beft, "\nafter: ", show aft, "\nperm: ", show p, "\nputting in the middle: ", show bind]
             if isFree 0 beft || isFree (ctxLen beft + ctxLen aft) t
               then return (bind <| beft, aft, p ++> 1)
               else do let aftP = insertP 0 (idP (ctxLen beft))
                       -- traceTCM_ ["applying aftP :", show aftP, "\non ", show aft]
                       return (beft, lift (ctxLen beft) 0 bind <|
                                     applyPerm aftP aft,
                               insertP (ctxLen aft) p)
