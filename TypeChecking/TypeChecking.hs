{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
    FlexibleInstances, TypeSynonymInstances
  #-}

module TypeChecking.TypeChecking where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader

import Data.Maybe
import Data.Monoid

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.InternaltoAbstract
import Syntax.Common
import Syntax.Position
import Syntax.Size
import qualified Syntax.Abstract as A
import TypeChecking.Conversion
import TypeChecking.TCM
import TypeChecking.TCMErrors
import TypeChecking.Whnf
import TypeChecking.Inductive (inferInd)
import TypeChecking.Fix (inferFix)
import TypeChecking.Case (inferCase)
import qualified TypeChecking.PrettyTCM as PP ((<>))
import TypeChecking.PrettyTCM hiding ((<>))
import Utils.Fresh


checkSort :: (MonadTCM tcm) => A.Sort -> tcm (Term, Type)
checkSort A.Prop     = do return (Sort Prop, Sort (Type 0))
checkSort (A.Type n) = do return (Sort (Type n), Sort (Type (1+n)))

checkProd :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
checkProd (Type _) Prop = return Prop
checkProd Prop (Type n) = return $ Type n
checkProd (Type m) (Type n) = do traceTCM 30 $ hsep [text "check product",
                                                     prettyPrintTCM m,
                                                     prettyPrintTCM n]
                                 return $ Type (max m n)

maxSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
maxSort (Type m) Prop = return $ Type m
maxSort Prop (Type n) = return $ Type n
maxSort (Type m) (Type n) = do traceTCM 30 $ hsep [text "max sort",
                                                   prettyPrintTCM m,
                                                   prettyPrintTCM n]
                               return $ Type (max m n)

isSort :: (MonadTCM tcm) => Range -> Term -> tcm Sort
isSort rg t = do t' <- whnF t
                 case t' of
                   Sort s -> return s
                   _      -> throwNotSort rg t'

-- We assume that in the global environment, types are normalized

inferBinds :: (MonadTCM tcm) => A.Context -> tcm (Context, Sort)
inferBinds CtxEmpty = return (CtxEmpty, Prop)
inferBinds (b :> bs) = do (ctx1, s1) <- inferBind b
                          (ctx2, s2) <- pushCtx ctx1 $ inferBinds bs
                          s' <- maxSort s1 s2
                          return (ctx1 <> ctx2, s')
  where
    inferBind (A.Bind _ [] _) = __IMPOSSIBLE__
    inferBind (A.Bind _ (x:xs) e) = do
      (t1, r1) <- infer (fromJust (implicitValue e))
      s1 <- isSort (range e) r1
      return (ctxFromList (mkCtx (x:xs) t1 0), s1)
        where
          impl = isImplicit e
          mkCtx [] _ _ = []
          mkCtx (y:ys) t k = mkImplBind y impl (I.lift k 0 t) : mkCtx ys t (k + 1)


infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort (range u) r
                         t' <- check t u'
                         w <- whnF u'
                         return (t', w)
infer (A.Sort _ s) = checkSort s
infer exp@(A.Pi _ ctx t) =
  do traceTCM 30 $ hsep [text "Inferring product",
                         prettyPrintTCM exp]
     (ctx', s1) <- inferBinds ctx
     (t', r2) <- pushCtx ctx' $ infer t
     s2 <- pushCtx ctx' $ isSort (range t) r2
     s' <- checkProd s1 s2
     return (mkPi ctx' t', Sort s')
infer exp@(A.Arrow _ e1 e2) = -- TODO: check arrows with implicit arguments
  do traceTCM 30 $ hsep [text "Inferring arrow",
                         prettyPrintTCM exp]
     (t1, r1) <- infer (implicitValue e1)
     s1 <- isSort (range e1) r1
     (t2, r2) <- pushType t1 $ infer e2
     s2 <- pushType t1 $ isSort (range e2) r2
     s' <- checkProd s1 s2
     return (mkPi (ctxSingle (unNamed t1)) t2, Sort s')
infer (A.Bound _ _ n) =
  do len <- localLength
     traceTCM 30 $ vcat [ text "infer Bound" <+> prettyPrintTCM n
                        , text "in ctx   " <+> (ask >>= prettyPrintTCM) ]
     when (n >= len) $
       traceTCM levelBug $ hsep [text "Context shorter than expected ",
                                 int len, text " <= ", int n]
     b <- localGet n
     w <- whnF (I.lift (n + 1) 0 (bindType b))
     return (Bound n, w)
infer (A.Ident _ x) =   do t <- getGlobal x
                           case t of
                             Definition {} -> return (Var x, defType t)
                             Assumption {} -> return (Var x, assumeType t)
                             _             -> __IMPOSSIBLE__
infer xx@(A.Lam _ bs t) =   do (ctx, _) <- inferBinds bs
                               (t', u) <- pushCtx ctx $ infer t
                               return (mkLam (eraseSize ctx) t', mkPi ctx u)
infer (A.App _ e1 e2) = -- inferApp e1 e2
    do (t1, r1) <- infer e1
       traceTCM 30 $ vcat [ text "Checking function part"
                          , text "from" <+> prettyPrintTCM e1
                          , text "to" <+> prettyPrintTCM t1
                          , text "of type" <+> prettyPrintTCM r1]
       case r1 of
         Pi ctx u2 ->
             do let (ch, ct) = ctxSplit ctx
                t2 <- check e2 (bindType ch)
                w  <- whnF $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u2)
                traceTCM 30 $ hsep [ text "Checked APP:"
                                   , prettyPrintTCM (mkApp t1 [t2]) ]
                traceTCM 30 $ hsep [ text "APP result type:"
                                   , prettyPrintTCM w ]
                return (mkApp t1 [t2], w)
         _            -> throwNotFunction r1
infer (A.Meta r _) = typeError $ CannotInferMeta r
infer (A.Ind _ an x ps) =
    do t <- getGlobal x
       i <- fresh
       -- when (an == Star) $ addStarStage i
       case t of
         ind@(Inductive {}) ->
           do
             ps' <- checkList ps (indPars ind)
             let indices = foldr subst (indIndices ind) ps'
             return (Ind (Size (Svar i)) x ps', mkPi indices (Sort (indSort ind)))
         _                             -> __IMPOSSIBLE__
infer (A.Constr _ x _ pars) = do
  t <- getGlobal x
  stage <- fresh
  let -- Star signals recursive occurrences of the inductive type. See TypeChecking.Inductive
      replStage x = if x == Star then (Size (Svar stage)) else x
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = Size (Hat (Svar stage))
          coDom = mkApp (Ind indStage indName (map Bound (reverse [numArgs..numArgs+numPars-1])))  indices
          resType = foldr subst (mkPi (replFunc targs) coDom) pars'
      traceTCM 20 $ vcat [ text "constructor TYPE:" <+> prettyPrintTCM resType ]
      -- We erase the type annotations of both parameters and arguments
      return (Constr x (indName, idConstr) (eraseSize pars'),
              resType)

    _  -> __IMPOSSIBLE__

infer (A.Fix f) = inferFix f
infer (A.Case c) = inferCase c
infer (A.Number _ _) = __IMPOSSIBLE__ -- Number n is transformed into S (S... O)) during scope checking

-- | Only inductive definitions return more than one global
inferDecl :: (MonadTCM tcm) =>  A.Declaration -> tcm [(Named Global)]
inferDecl (A.Definition _ x (Just e1) e2) =
    do (tp, s) <- infer e1
       _ <- isSort (range e1) s
       def <- check e2 tp
       return [mkNamed x (Definition { defType = tp
                                     , defTerm = def })]
inferDecl (A.Definition _ x Nothing e) =
    do (def, tp) <- infer e
       return [mkNamed x (Definition { defType = tp
                                     , defTerm = def })] -- (flatten u) (flatten t))]
inferDecl (A.Assumption _ x e) =
    do (t, r) <- infer e
       _ <- isSort (range e) r
       return [mkNamed x (Assumption t)] -- (flatten t))]
inferDecl (A.Inductive _ indDef) = inferInd indDef
inferDecl (A.Eval e) =
    do (e1, t1) <- infer e
       r <- reify e1
       traceTCM 70 $ hsep [text "eval ", prettyPrintTCM e1 PP.<> dot]
       e1' <- nF e1
       traceTCM 70 $ vcat [text "Normal form obtained ", prettyPrintTCM e1']
       printTCMLn $ prettyPrintTCM e1'
       return []
inferDecl (A.Check e1 (Just e2)) =
    do (t2, r2) <- infer e2
       _ <- isSort (range e2) r2
       t1 <- check e1 t2
       traceTCM 70 $ hsep [text "check ", prettyPrintTCM t1, text " : "]
       printTCMLn $ prettyPrintTCM t2
       return []
inferDecl (A.Check e1 Nothing) =
    do (t1, u1) <- infer e1
       -- traceTCM_ ["checking ", show e1, "\ngiving ", show t1, "\n of type ", show u1]
       traceTCM 70 $ hsep [text "check ", prettyPrintTCM t1, text " : "]
       printTCMLn $ prettyPrintTCM u1
       return []




check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term
check (A.Meta r Nothing) u = do
  m <- fresh
  e <- ask
  addGoal m (mkGoal e u)
  return (Meta m)
check t u =   do traceTCM 30 $ (hsep [text "Checking type of", prettyPrintTCM t]
                                <+> hsep [text "against", prettyPrintTCM u])
                 (t', r) <- infer t
                 traceTCM 30 $ hsep [text "Calling subtype with ", prettyPrintTCM r,
                                     text "≤", prettyPrintTCM u]
                 b <- r `subType` u
                 unless b $ throwNotConvertible (Just (range t)) r u
                 return t'


checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]
checkList es CtxEmpty = return []
checkList (e:es) (b :> bs) =
  do
    traceTCM 30 $ vcat [ text "checkList" <+> prettyPrintTCM (e:es)
                       , text "against" <+> prettyPrintTCM (b :> bs) ]
    t <- check e (bindType b)
    ts <- checkList es (subst t bs)
    return (t:ts)
checkList es ctx =
  do
    traceTCM 30 $ vcat [ text "checkList" <+> prettyPrintTCM es
                       , text "against" <+> prettyPrintTCM ctx ]
    __IMPOSSIBLE__
