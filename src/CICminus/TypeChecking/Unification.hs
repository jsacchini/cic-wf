{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CICminus.TypeChecking.Unification where

import           Control.Monad
import           Control.Monad.Reader              hiding (lift)
import qualified Control.Monad.Reader              as R (lift)
import           Data.List
import           Data.Monoid

import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal          as I
import           CICminus.Syntax.Position

import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.Permutation
import           CICminus.TypeChecking.PrettyTCM   hiding ((<>))
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.Whnf

import           CICminus.Utils.Maybe
import           CICminus.Utils.Misc
import           CICminus.Utils.Sized

-- | An equation is just a pair of terms
type Equation = (Term, Term)

instance SubstTerm Equation where
  substN k t (t1, t2) = (substN k t t1, substN k t t2)


-- | unifyPos returns the unification if it succeedes positively or throws an
--   exception if unification succeedes negatively or fails
unifyPos :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm (Context, Permutation, [Int])
unifyPos ctx eqs ks =
  do
    traceTCM 30 $ vcat [ text "UNIFY POS"
                       , text "in env:" <+> (ask >>= prettyTCM)
                       , text "in context:" <+> prettyTCM ctx
                       , text "EQs" <+> (pushCtx ctx $ prettyTCM eqs)
                       , text "FOR" <+> prettyTCM ks ]
    r <- runMT $ unify ctx eqs ks
    case r of
      Just x@(ctxr, permr, ksr) ->
        do
          traceTCM 30 $ vcat [ text "UNIFY POS RESULT"
                             , text "in env:" <+> (ask >>= prettyTCM)
                             , text "result context:" <+> prettyTCM ctxr
                             , text "perm result" <+> prettyTCM (unPerm permr)
                             , text "for result" <+> prettyTCM ksr ]
          return x
      Nothing -> typeError $ NotUnifiable 1


-- | unifyNeg returns () if the unification succeedes negatively or throws an
--   exception if unification succeedes positively or fails. It is called for
--   impossible branches
unifyNeg :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm ()
unifyNeg ctx eqs ks =
  do
    traceTCM 30 $ vcat [ text "UNIFY NEG"
                       , text "in env:" <+> (ask >>= prettyTCM)
                       , text "in context:" <+> prettyTCM ctx
                       , text "EQs" <+> prettyTCM eqs
                       , text "FOR" <+> prettyTCM ks ]
    r <- runMT $ unify ctx eqs ks
    case r of
      Just x -> typeError (NotImpossibleBranch noRange)
      Nothing -> return ()


-- | unify G (u = v) s computes the first-order unification of 'u' and 'v' under
--   context G, with s indicating the subset of variables of G open to
--   unification.
--
--   If unification succeeds positively, it returns a new context G' which is a
--   reorder of G where unified variables are turned to local definitions, a
--   permutation p and the set of variables s' that were not unified.
--   Permutation p has the following meaning: if a term 't' is well-scoped in
--   context G, then 'applyPerm p t' is well-scoped in G'.
--
--   If unification suceeds negatively, it returns Nothing. If unification fails
--   (problem too complicated) it throws an exception.
unify :: (MonadTCM tcm) =>
         Context -> [Equation] -> [Int] ->
         MaybeT tcm (Context, Permutation, [Int])
unify ctx [] ks = return (ctx, idP (size ctx), ks)
unify ctx ((t1,t2):es) ks = do

  -- Normalize the first equation
  -- traceTCM_ ["Unifying equation ", show ctx, "\neq  ", show t1, " === ", show t2, "\nfor ", show ks, "\nrest of eqs: ", show es]
  w1 <- R.lift $ pushCtx ctx $ whnF t1
  w2 <- R.lift $ pushCtx ctx $ whnF t2
  -- traceTCM_ ["Normalized equation: ", show w1, " === ", show w2, "\nfor ", show ks]

  -- Unify the first equation
  R.lift $ traceTCM 30 $ vcat [ text "unifying equation" <+> prettyTCM (length es + 1)
                              , text "ctx" <+> prettyTCM ctx
                              , text "EQ " <+> (pushCtx ctx $ prettyTCM (w1, w2))
                              , text "for"
                              , prettyTCM ks ]
  (ctx1, p1, ks1) <- unifyEq ctx (w1,w2) ks
  R.lift $ traceTCM 30 $ vcat [ text "result"
                              , prettyTCM ctx1
                              , text "perm" <+> prettyTCM (unPerm p1)
                              , text "for"
                              , prettyTCM ks1 ]
  -- traceTCM_ ["result unifyEq ", show ctx1, " left ", show ks1, "\n perm : ", show p1]
  -- traceTCM_ ["REST ", show ctx1, "\neq  ", show $ map (applyPerm p1) es, "\nfor ", show ks1]

  -- Unify the rest of the equations applying
  (ctx2, p2, ks2) <- unify ctx1 (map (applyPerm p1) es) ks1
  -- e <- R.lift $ ask
  -- R.lift $ traceTCM_ ["Combining all\nouter context: ", show e, "\nstarting ", show ctx, "\nopen vars: ", show ks, "\n\nfirst eq: ", show (w1,w2), "\nresult: ", show ctx1, "\nperm: ", show p1, "\nleft: ", show ks1, "\n\nrest of eq ", show es, "\nctx: ", show ctx2, "\nleft ", show ks2, "\n perm : ", show p2] --, "\n combining perm: "] -- , show $ combineP p2 p1]

  -- Combine the results of both unifications
  return (ctx2, combineP p2 p1, ks2)




-- | unifyEq unifies just one equation. The equation must be in whnf
unifyEq :: (MonadTCM tcm) =>
           Context -> Equation -> [Int] -> MaybeT tcm (Context, Permutation, [Int])
unifyEq ctx (Bound k1, Bound k2) js
  -- if k1 is an open variable, we unify it calling applyDef
  | k1 `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k1 (Bound k2)
                      -- traceTCM_ ["applyDef left result ", show ctx', "\nperm ", show p]
                      return (ctx', p, applyPerm p (js \\ [k1]))
  | k2 `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k2 (Bound k1)
                      -- traceTCM_ ["applyDef right result ", show ctx', "\nperm ", show p]
                      return (ctx', p, applyPerm p (js \\ [k2]))
  | otherwise    =
    do
      unless (k1 == k2) $ R.lift $ (do traceTCM 1 $ vcat [ text "NOT UNIFIABLE"
                                                         , text "env:" <+> (ask >>= prettyTCM)
                                                         , hsep [text "unif:", text "bound", prettyTCM k1, text "and bound", prettyTCM k2, text "for", prettyTCM js]
                                                         ]
                                       typeError $ NotUnifiable 2)
      return (ctx, idP (size ctx), js)
unifyEq ctx (Bound k, t2) js
  | k `elem` js = do (ctx', p) <- R.lift $ applyDef ctx k t2
                     -- traceTCM_ ["applyDef left result ", show ctx', "\nperm ", show p]
                     return (ctx', p, applyPerm p (js \\ [k]))
  | otherwise   = do (unlessM (R.lift $ conv (Bound k) t2)) $ R.lift $ typeError $ NotUnifiable 3 -- TODO: revise this line, as it should not be used. The pattern (Bound, Bound) is covered by the first case
                     return (ctxEmpty, idP (ctxLen ctx), js)
unifyEq ctx (t1, Bound k) js = unifyEq ctx (Bound k, t1) js

-- If both terms are in constructor form, we unify the arguments if the
-- constructor is the same, or return negative success (Nothing) if they are
-- different.
-- TODO: check that Constr are not in sort Prop
unifyEq ctx (App (Constr x1 cid1 ps1) as1, App (Constr x2 cid2 ps2) as2) js =
  if x1 == x2
  then do -- traceTCM_ ["unifying constructor ", show x1, "\nnew equations: ", show (zip as1 as2)]
          unify ctx (zip as1 as2) js
  else fail "Negative sucess"
-- Otherwise, we have to check that both terms are convertible. If they are not
-- the problem is too difficult and we raise an exception.
unifyEq ctx (t1, t2) js =
  do unlessM (R.lift $ conv t1 t2) $ R.lift $ typeError $ NotUnifiable 4
     return (ctxEmpty, idP (ctxLen ctx), js)




-- | 'applyDef G k t = (T, p)' where
--
--   * 'T' is a well-formed reorder of 'G' given by 'p', and
--   * the 'k'-th variable of G is assigned to 't'
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
     return (ctx1 <> cxa' <> (Bind x False u' (Just t') :> cxb'), p')
  where (ctx1, ctx0') = ctxSplitAt (ctxLen ctx - k - 1) ctx
        (Bind x _ u Nothing, ctx0) = ctxSplit ctx0'

-- | strengthen G t = (G0, G1, p)
--
--   * assumes that 't' is well-typed in G
--   * returns a reorder of 'G' given by 'p' where 'G0' is the part of 'G'
--     needed to type-check 't' and 'G1' is the rest
strengthen :: MonadTCM tcm =>
              Context -> Term -> tcm (Context,Context,Permutation)
strengthen CtxEmpty _ = return (CtxEmpty, CtxEmpty, Perm [])
strengthen (bnd :> ctx) t = do
  (ctx0, ctx1, p) <- strengthen ctx t
  -- traceTCM_ ["in strengthen\nbefore: ", show ctx0, "\nctx1er: ", show ctx1, "\nperm: ", show p, "\nputting in the middle: ", show bnd]

  -- Let bnd = (x : u) or (x := u1 : u2)
  -- If x (bound var 0) is free in ctx0, or in 't' then we add bnd to ctx0,
  -- otherwise, we add bnd to ctx1. In both cases, the permutation is adjusted
  -- as needed
  if isFree 0 ctx0 || isFree (ctxLen ctx0 + ctxLen ctx1) t
    then return (bnd :> ctx0, ctx1, p ++> 1)
    else do
      -- We need to shift the vars in bnd by ctx0;
      -- adjust the position of bnd in ctx1 (using permutation ctx1P); and
      -- adjust the returned permutation by inserting bnd in the correct place
      let ctx1P = insertP 0 (idP (ctxLen ctx0))
      -- traceTCM_ ["applying ctx1P :", show ctx1P, "\non ", show ctx1]
      return (ctx0, lift (ctxLen ctx0) 0 bnd :> applyPerm ctx1P ctx1,
              insertP (ctxLen ctx1) p)
