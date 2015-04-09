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

module CICwf.TypeChecking.Match where

import           Control.Monad
import           Control.Monad.Reader     hiding (lift)
import qualified Control.Monad.Reader     as R (lift)
import           Data.List
import           Data.Monoid

import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal          as I
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.Conversion
-- import           CICwf.TypeChecking.Permutation
import           CICwf.TypeChecking.PrettyTCM   hiding ((<>))
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.Whnf

import           CICwf.Utils.Maybe
import           CICwf.Utils.Misc
import           CICwf.Utils.Sized

-- | An equation is just a pair of terms
type Equation = (Term, SinglePattern)

instance SubstTerm Equation where
  substN k t (t1, t2) = (substN k t t1, substN k t t2)


-- | matchPos returns the unification if it succeedes positively or throws an
--   exception if unification succeedes negatively or fails
matchPos :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm (Context, [Int])
matchPos ctx eqs ks =
  do
    traceTCM 30 $ vcat [ text "UNIFY POS"
                       , text "in env:" <+> (ask >>= prettyTCM)
                       , text "in context:" <+> prettyTCM ctx
                       , text "EQs" <+> (pushCtx ctx $ prettyTCM eqs)
                       , text "FOR" <+> prettyTCM ks ]
    r <- runMT $ match ctx eqs ks
    case r of
      Just x@(ctxr, ksr) ->
        do
          traceTCM 30 $ vcat [ text "UNIFY POS RESULT"
                             , text "in env:" <+> (ask >>= prettyTCM)
                             , text "result context:" <+> prettyTCM ctxr
                             , text "for result" <+> prettyTCM ksr ]
          return x
      Nothing -> typeError' $ NotUnifiable eqs


-- | matchNeg returns () if the unification succeedes negatively or throws an
--   exception if unification succeedes positively or fails. It is called for
--   impossible branches
matchNeg :: (MonadTCM tcm) =>
            Context -> [Equation] -> [Int] -> tcm ()
matchNeg ctx eqs ks =
  do
    traceTCM 30 $ vcat [ text "UNIFY NEG"
                       , text "in env:" <+> (ask >>= prettyTCM)
                       , text "in context:" <+> prettyTCM ctx
                       , text "EQs" <+> prettyTCM eqs
                       , text "FOR" <+> prettyTCM ks ]
    r <- runMT $ match ctx eqs ks
    case r of
      Just _ -> typeError noRange NotImpossibleBranch
      Nothing -> return ()


-- | match 'G' ('us' = 'vs') 'vars' computes the first-order matching of 'us'
--   and 'vs' under context 'G', with 'vars' indicating the subset of variables
--   of G open to substitution. 'vs' must be ground in 'G', meaning that
--   variables in 'vars' cannot be free in 'vs'. Furthermore, free variables in
--   'vs' must be greater than all variables in 'vars'. This means that no
--   reordering of 'G' would be required.
--
--   If matching succeeds positively, it returns a new context G0 which is G
--   where matched variables are turned to local definitions and the set of
--   variables s' that were not matched.
--
--   If matching suceeds negatively, it returns Nothing. If matching fails
--   (problem too complicated) it throws an exception.
match :: (MonadTCM tcm) =>
         Context -> [Equation] -> [Int] ->
         MaybeT tcm (Context, [Int])
match ctx [] ks           = return (ctx, ks)
match ctx ((_, PatternVar _):es) ks = match ctx es ks
match ctx ((t1,PatternDef _ t2):es) ks = do

  -- Normalize the first equation
  R.lift $ pushCtx ctx $ traceTCM 40 $ vcat [ text "matching eq in context" <+> (ask >>= prettyTCM)
                     , prettyTCM t1 <+> text " === "
                       <+>  prettyTCM t2
                     , text "for ", prettyTCM ks
                     , text "rest of eqs: ", prettyTCM es ]
  w1 <- R.lift $ pushCtx ctx $ whnf t1
  w2 <- R.lift $ pushCtx ctx $ whnf t2

  R.lift $ pushCtx ctx $ traceTCM 40 $ hsep [ text "Normalized equation: "
                     , prettyTCM w1 <+> text " === "
                       <+>  prettyTCM w2 ]

  R.lift $ pushCtx ctx $ traceTCM 40 $ hsep [ text "Unifying: "
                     , prettyTCM w1 <+> text " === "
                       <+>  prettyTCM w2 ]
  -- Unify the first equation
  (ctx1, ks1) <- matchEq ctx (w1,w2) ks
  R.lift $ pushCtx ctx1 $ traceTCM 40 $ vcat [ text "result matchEq"
                              , prettyTCM ctx1
                              , text "for"
                              , prettyTCM ks1 ]
  -- traceTCM_ ["result unifyEq ", show ctx1, " left ", show ks1, "\n perm : ", show p1]
  -- traceTCM_ ["REST ", show ctx1, "\neq  ", show $ map (applyPerm p1) es, "\nfor ", show ks1]

  -- Unify the rest of the equations applying
  (ctx2, ks2) <- match ctx1 es ks1
  -- e <- R.lift $ ask
  -- R.lift $ traceTCM_ ["Combining all\nouter context: ", show e, "\nstarting ", show ctx, "\nopen vars: ", show ks, "\n\nfirst eq: ", show (w1,w2), "\nresult: ", show ctx1, "\nperm: ", show p1, "\nleft: ", show ks1, "\n\nrest of eq ", show es, "\nctx: ", show ctx2, "\nleft ", show ks2, "\n perm : ", show p2] --, "\n combining perm: "] -- , show $ combineP p2 p1]

  -- Combine the results of both unifications
  return (ctx2, ks2)




-- | matchEq unifies just one equation. The equation must be in whnf
matchEq :: (MonadTCM tcm) =>
           Context -> (Term, Term) -> [Int] ->
           MaybeT tcm (Context, [Int])
matchEq ctx (Bound k, t2) js
  | k `elem` js = do
    R.lift $ pushCtx ctx $ traceTCM 35 $ hsep [ text "Matching"
                                , prettyTCM k
                                , text ":="
                                , prettyTCM t2
                                , parens (text (show t2))]
    R.lift $ traceTCM 35 $ hsep [ text "Initial context"
                                , prettyTCM ctx ]
    R.lift $ traceTCM 35 $ hsep [ text "Applied context"
                                , prettyTCM (applyCtxDef ctx k (lift0 (-k-1) t2)) ]
    return (revapplyCtxDef ctx k (lift0 (-k-1) t2), js \\ [k])
  | otherwise   = do (unlessM (R.lift $ pushCtx ctx $ conv (Bound k) t2)) $ R.lift $ typeError' $ NotUnifiable [(Bound k, PatternDef noName t2)] -- TODO: revise this line, as it should not be used. The pattern (Bound, Bound) is covered by the first case
                     return (ctx, js)
matchEq ctx (App (Constr x1 cid1 ps1) as1, App (Constr x2 cid2 ps2) as2) js
  | x1 == x2  = match ctx (zip as1 (map (PatternDef noName) as2)) js
  | otherwise = fail "Negative sucess"
matchEq ctx (Constr x1 cid1 ps1, App (Constr x2 cid2 ps2) as2) js
  | x1 == x2  = match ctx (zip [] (map (PatternDef noName) as2)) js
  | otherwise = fail "Negative sucess"
matchEq ctx (App (Constr x1 cid1 ps1) as1, Constr x2 cid2 ps2) js
  | x1 == x2  = match ctx (zip as1 []) js
  | otherwise = fail "Negative sucess"
-- Otherwise, we have to check that both terms are convertible. If they are not
-- the problem is too difficult and we raise an exception.
matchEq ctx (t1, t2) js = do
  R.lift $ traceTCM 40 $ pushCtx ctx $ hsep [ text "testing conversion"
                                            , text (show t1)
                                            , text "and "
                                            , text (show t2) ]
  unlessM (R.lift $ pushCtx ctx $ conv t1 t2) $
    do R.lift $ traceTCM 40 $ hsep [ text "conversion failed"
                                   , text (show t1)
                                   , text "and "
                                   , text (show t2) ]
       R.lift $ typeError' $ NotUnifiable [(t1, PatternDef noName t2)]
  return (ctxEmpty, js)
