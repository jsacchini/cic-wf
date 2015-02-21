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

{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module CICminus.TypeChecking.TypeChecking where

import           CICminus.Utils.Impossible

import           Control.Monad.Reader
import           Data.Monoid

import qualified CICminus.Syntax.Abstract           as A
import           CICminus.Syntax.AbstractToConcrete as AC
import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal           hiding (lift)
import           CICminus.Syntax.Internal           as I
import           CICminus.Syntax.Position
import           CICminus.TypeChecking.Case         (inferCase)
import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.Fixpoint     (inferFix)
import           CICminus.TypeChecking.PrettyTCM    hiding ((<>))
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.TCMErrors
import           CICminus.TypeChecking.Whnf
import           CICminus.Utils.Fresh
import           CICminus.Utils.Misc



checkSort :: (MonadTCM tcm) => Sort -> tcm (Term, Type)
checkSort Prop     = return (Sort Prop, Sort (Type 0))
checkSort (Type n) = return (Sort (Type n), Sort (Type (1+n)))


checkProd :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
checkProd (Type _) Prop = return Prop
checkProd Prop (Type n) = return $ Type n
checkProd (Type m) (Type n) = do
  traceTCM 35 $ hsep [ text "check product"
                     , prettyTCM m
                     , prettyTCM n]
  return $ Type (max m n)


maxSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
maxSort (Type m) Prop = return $ Type m
maxSort Prop (Type n) = return $ Type n
maxSort (Type m) (Type n) = do
  traceTCM 35 $ hsep [ text "max sort"
                     , prettyTCM m
                     , prettyTCM n]
  return $ Type (max m n)


isSort :: (MonadTCM tcm) => Range -> Term -> Type -> tcm Sort
isSort rg t u = do
  u' <- whnf u
  case u' of
    Sort s -> return s
    _      -> typeError rg $ NotSort t u


inferType :: (MonadTCM tcm) => A.Expr -> tcm (Type, Sort)
inferType e = do
  (tp, s) <- infer e
  s0 <- isSort (range e) tp s
  return (tp, s0)

-- We assume that in the global environment, types are normalized

inferBinds :: (MonadTCM tcm) => A.Context -> tcm (Context, Sort)
inferBinds CtxEmpty = return (CtxEmpty, Prop)
inferBinds (b :> bs) = do
  (ctx1, s1) <- inferBind b
  traceTCM 40 $ text "Bind inferred: " <+> prettyTCM ctx1
  (ctx2, s2) <- pushCtx ctx1 $ inferBinds bs
  s' <- maxSort s1 s2
  return (ctx1 <> ctx2, s')
    where
      inferBind (A.Bind _ [] _) = __IMPOSSIBLE__
      inferBind (A.Bind _ (x:xs) e) = do
        (t1, s1) <- inferType (unArg e)
        return (ctxFromList (mkCtx (x:xs) t1 0), s1)
          where
            mkCtx [] _ _ = []
            mkCtx (y:ys) t k = mkBind y (I.lift k 0 t) : mkCtx ys t (k + 1)


infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do
  (u', r) <- inferType u
  t' <- check t u'
  w <- whnf u'
  return (t', w)

infer (A.Sort _ s) = checkSort s

infer expr@(A.Pi _ ctx t) = do
  traceTCM 35 $ hsep [text "Inferring product",
                      prettyTCM expr]
  (ctx', s1) <- inferBinds ctx
  (t', s2) <- pushCtx ctx' $ inferType t
  s' <- checkProd s1 s2
  return (mkPi ctx' t', Sort s')

infer (A.Local _ x) = do
  (n, b) <- localGetByName x
  traceTCM 35 $ vcat [ text "infer Bound" <+> prettyTCM n
                     , text "in ctx   " <+> (ask >>= prettyTCM) ]
  w <- whnf (I.lift (n + 1) 0 (unArg (bindType b)))
  traceTCM 35 $ text "inferred Local" <+> prettyTCM n <+> prettyTCM w
  return (Bound n, w)

infer (A.Global rg ident) = do
  gl <- getGlobal ident
  let ConstrType xs tp = case gl of
        Definition {} -> defType gl
        Assumption {} -> assumeType gl
        Cofixpoint {} -> cofixType gl
        _             -> __IMPOSSIBLE__
  tp' <- instantiate xs tp
  traceTCM 30 $ vcat [text "instantiate" <+> prettyTCM (ConstrType xs tp)
                     , text "to" <+> prettyTCM tp' ]
  return (Var ident, tp')
    where
      instantiate :: (MonadTCM tcm) => [Name] -> Type -> tcm Type
      instantiate [] tp = return tp
      instantiate (x:xs) tp = do
        sta <- freshStage rg
        let replStage (SizeVar nm k) | x == nm = Stage (StageVar sta k)
                                     | otherwise = SizeVar nm k
            replStage s = s
        instantiate xs (modifySize replStage tp)

infer (A.SApp rg _ _) = notImplemented rg "TODO: infer SApp"

infer (A.Lam _ bs t) = forbidAnnot $ do
  (ctx, _) <- inferBinds bs
  pushCtx ctx $
    traceTCM 35 $ vcat [ text "inferring Lam body" <+> prettyTCM t
                       , text "in ctx   " <+> (ask >>= prettyTCM) ]
  (t', u) <- pushCtx ctx $ infer t
  traceTCM 35 $ text "inferred Lam body" <+> text (show t')
  return (mkLam (eraseSize ctx) t', mkPi ctx u)

infer (A.App _ e1 _ e2) = do -- inferApp e1 e2
  (t1, r1) <- infer e1
  traceTCM 35 $ vcat [ text "Checking function part"
                     , text "from" <+> prettyTCM e1
                     , text "to" <+> prettyTCM t1
                     , text "of type" <+> prettyTCM r1]
  case r1 of
    Pi ctx u2 -> do
      let (ch, ct) = ctxSplit ctx
      t2 <- forbidAnnot $ check e2 (unArg (bindType ch))
      w  <- whnf $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u2)
      traceTCM 35 $ hsep [ text "Checked APP:"
                         , prettyTCM (mkApp t1 [t2]) ]
      traceTCM 35 $ hsep [ text "APP result type:"
                         , prettyTCM w ]
      return (mkApp t1 [t2], w)
    _            -> typeError (range e1) $ NotFunction t1 r1

infer (A.Meta r _) = typeError r CannotInferMeta

infer i@(A.Ind r x sexpr pars) = do
  -- Get Inductive; for well-scoped terms, this should not fail
  traceTCM 40 $ text "Typechecking (co)inductive type:" <+> prettyTCM i <+> text (show sexpr) <+> text "applied to" <+> prettyTCM pars

  ind@Inductive{} <- getGlobal x
  pars' <- checkList pars (indPars ind)
  let indices = foldr subst (indIndices ind) pars'
  annot <- inferSizeExpr sexpr r
  traceTCM 40 $ text "Typechecked:" <+> prettyTCM (Ind annot x pars')
    <+> text "of type" <+> prettyTCM (mkPi indices (Sort (indSort ind)))
  return (Ind annot x pars',
          mkPi indices (Sort (indSort ind)))

    where
      inferSizeExpr (A.SizeStar rg) _ = do
        unlessM isStarAllowed $ notImplemented rg "star annotation not allowed"
        stage <- freshStage rg
        addStarStageVar stage
        return $ I.Stage (I.StageVar stage 0)

      inferSizeExpr (A.SizeExpr rg nm k) _ = do
        unlessM isSizeAllowed $ notImplemented rg "size annotations not allowed"
        -- stage <- getSize nm
        return $ I.SizeVar nm k -- I.Stage (I.StageVar stage k)

      inferSizeExpr A.SizeEmpty rg = do
        stage <- freshStage rg
        traceTCM 40 $ text ("fresh stage " ++ show stage)
        return $ I.Stage (I.StageVar stage 0)

infer (A.Constr rg x pars) = forbidAnnot $ do
  t <- getGlobal x
  stage <- freshStage rg
  traceTCM 35 $ hsep [ text "fresh stage"
                     , prettyTCM stage
                     , text "at"
                     , prettyTCM rg ]
  let -- Star signals recursive occurrences of the inductive type. See CICminus.TypeChecking.Inductive
      replStage s = if s == I.Star then I.Stage (I.StageVar stage 0) else s
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = I.Stage (I.StageVar stage 1)
          coDom = mkApp (Ind indStage indName (map Bound (reverse [numArgs..numArgs+numPars-1])))  indices
          resType = foldr subst (mkPi (replFunc targs) coDom) pars'
      traceTCM 20 $ vcat [ text "constructor TYPE:" <+> prettyTCM resType ]
      -- We erase the type annotations of both parameters and arguments
      return (Constr x (indName, idConstr) (eraseSize pars'),
              resType)

--     _  -> __IMPOSSIBLE__

infer (A.Fix f) = forbidAnnot $ do
  (f', tp, _) <- inferFix f -- inferNoTerm f
  return (Fix f', tp)

infer (A.Case c) = forbidAnnot $ inferCase c

-- infer (A.Number _ _) = __IMPOSSIBLE__ -- Number n is transformed into S (S... O)) during scope checking






check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term
check (A.Meta _ Nothing) u = do
  m <- fresh
  e <- ask
  addGoal m (mkGoal e u)
  return (Meta m)

check t u = do
  traceTCM 35 $ hsep [ text "Checking type of", prettyTCM t
                     , text "against", prettyTCM u]
  (t', r) <- infer t
  traceTCM 35 $ hsep [text "Calling subtype with ", prettyTCM r,
                      text "≤", prettyTCM u]
  traceTCM 35 $ hsep [text "Calling subtype with ", text (show r),
                      text "≤", text (show u)]
  b <- r `subType` u
  unless b $ typeError (range t) $ NotConvertible r u
  return t'


checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]
checkList _ CtxEmpty = return []
checkList (e:es) (b :> bs) =
  do
    concs <- AC.concretize (e : es)
    traceTCM 35 $ vcat [ text "checkList" <+> prettyTCM concs
                       , text "against" <+> prettyTCM (b :> bs) ]
    t <- check e (unArg (bindType b)) -- TODO
    ts <- checkList es (subst t bs)
    return (t:ts)
checkList es ctx =
  do
    concs <- AC.concretize es
    traceTCM 35 $ vcat [ text "checkList" <+> prettyTCM concs
                       , text "against" <+> prettyTCM ctx ]
    __IMPOSSIBLE__



checkSinglePattern :: (MonadTCM tcm) => A.SinglePattern -> Bind
                      -> tcm (SinglePattern, Bind)
checkSinglePattern (A.PatternVar _ x) b =
  return (PatternVar x, b { bindName = if isNull x
                                       then bindName b
                                       else x})
checkSinglePattern (A.PatternDef _ x e) b = do
  e' <- check e (unArg (bindType b))
  return (PatternDef x e',
          b { bindName = if isNull x
                         then bindName b
                         else x
            , bindDef = Just e' })


checkPattern :: (MonadTCM tcm) => A.Pattern -> Context
                -> tcm (Pattern, Context)
checkPattern []     CtxEmpty   = return ([], CtxEmpty)
checkPattern (p:ps) (b :> ctx) = do
  traceTCM 50 $ text "checking pattern"
    <+> prettyTCM (p:ps) <+> text "with ->" <+> prettyTCM (b :> ctx)
  (p', b') <- checkSinglePattern p b
  (ps', ctx') <- pushBind b' $ checkPattern ps ctx
  traceTCM 50 $ text "checked pattern"
    <+> prettyTCM (p' : lift0 (-1) ps')
    <+> text "of type" <+> prettyTCM (b' :> ctx')
  return (p' : lift0 (-1) ps', b' :> ctx')


inferNoTerm :: (MonadTCM tcm) => A.FixExpr -> tcm (FixTerm, Type)
inferNoTerm fix = do
  (ctx, _) <- inferBinds (A.fixArgs fix)
  (tp, r) <- pushCtx ctx $ inferType (A.fixType fix)
  let recTp = mkPi ctx tp
  (body, bodyTp) <- pushBind (mkBind (A.fixName fix) recTp)
                    $ pushCtx ctx $ infer (A.fixBody fix)
  unlessM (tp `conv` bodyTp)
    $ typeError (range fix) $ NotConvertible recTp bodyTp
  return (FixTerm { fixKind = A.fixKind fix
                  , fixNum  =
                    case A.fixSpec fix of
                      A.FixStruct _ i -> i
                      _               -> 0
                  , fixName = A.fixName fix
                  , fixSpec = FixStruct
                  , fixArgs = ctx
                  , fixType = tp
                  , fixBody = body }, recTp)
