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
{-# LANGUAGE PatternGuards          #-}

module CICwf.TypeChecking.TypeChecking where

#include "undefined.h"
import           CICwf.Utils.Impossible

import           Control.Monad.Reader
import           Data.Monoid

import qualified CICwf.Syntax.Abstract           as A
import           CICwf.Syntax.AbstractToConcrete as AC
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           hiding (lift)
import           CICwf.Syntax.Internal           as I
import           CICwf.Syntax.Position
import           CICwf.TypeChecking.Case         (inferCase)
import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.Fixpoint     (inferFix)
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors
import           CICwf.TypeChecking.Whnf
import           CICwf.Utils.Fresh
import           CICwf.Utils.Misc



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

infer (A.Local rg x) = do
  (n, b) <- localGetByName x
  traceTCM 35 $ vcat [ text "infer Bound" <+> prettyTCM n
                     , text "in ctx   " <+> (ask >>= prettyTCM) ]
  w <- whnf (I.lift (n + 1) 0 (unArg (bindType b)))
  case w of
    Subset i a t -> do
      alpha <- freshConstrainedStage rg a
      addWfConstraint (hat (mkAnnot alpha)) a
      let t' = substSizeName i (mkAnnot alpha) t
      w' <- whnf t'
      return (CBound n (mkAnnot alpha), w')
    _            -> return (Bound n, w)

infer (A.Global rg ident) = do
  gl <- getGlobal ident
  let ctp = case gl of
        Definition {} -> defType gl
        Assumption {} -> assumeType gl
        Cofixpoint {} -> cofixType gl
        _             -> __IMPOSSIBLE__
  case ctp of
    UnConstrType tp ->
      case tp of
        Subset i a t -> do
          alpha <- freshStage rg
          traceTCM 10 $ (text "Global constrained type:" <+> prettyTCM tp
                         $$ text "Adding constraint:" <+> prettyTCM (hat (mkAnnot alpha)) <+> text "<=" <+> prettyTCM a)
          addWfConstraint (hat (mkAnnot alpha)) a
          let t' = substSizeName i (mkAnnot alpha) t
          w' <- whnf t'
          return (CVar ident (mkAnnot alpha), w')
        _            -> return (Var ident, tp)
    ConstrType i tp -> do
      alpha1 <- freshStage rg
      let tp' = substSizeName i (mkAnnot alpha1) tp
      w' <- whnf tp'
      return (CVar ident (mkAnnot alpha1), w')


infer (A.SApp rg _ _ _) = notImplemented rg "TODO: infer SApp"

infer (A.Lam _ bs t) = forbidAnnot $ do
  (ctx, _) <- inferBinds bs
  pushCtx ctx $
    traceTCM 35 $ vcat [ text "inferring Lam body" <+> prettyTCM t
                       , text "in ctx   " <+> (ask >>= prettyTCM) ]
  (t', u) <- pushCtx ctx $ infer t
  traceTCM 35 $ text "inferred Lam body" <+> text (show t')
  return (mkLam ({- eraseSize -} ctx) t', mkPi ctx u)

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

infer i@(A.Ind r b x sexpr pars) = do
  -- Get Inductive; for well-scoped terms, this should not fail
  traceTCM 40 $ text "Typechecking (co)inductive type:" <+> prettyTCM i <+> text (show sexpr) <+> text "applied to" <+> prettyTCM pars

  ind@Inductive{} <- getGlobal x
  pars' <- checkList pars (indPars ind)
  let indices = foldr subst (indIndices ind) pars'
  annot <- inferSizeExpr sexpr r
  traceTCM 40 $ text "Typechecked:" <+> prettyTCM (Ind annot b x pars')
    <+> text "of type" <+> prettyTCM (mkPi indices (Sort (indSort ind)))
  return (Ind annot b x pars',
          mkPi indices (Sort (indSort ind)))

    where
      inferSizeExpr (A.SizeStar rg) _ = do
        unlessM isStarAllowed $ notImplemented rg "star annotation not allowed"
        stage <- freshStage rg
        addStarStageVar stage
        return $ I.Stage (I.StageVar stage 0)

      inferSizeExpr (A.SizeExpr rg nm k) _ = do
        unlessM isSizeAllowed $ notImplemented rg "size annotations not allowed"
        Just annot <- getSize nm
        traceTCM 40 $ text "Size expression: " <+> prettyTCM (hatn k annot)
        traceTCM 40 $ text "in map:" <+> (getSizeMap >>= prettyTCM)
        return $ hatn k annot

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
  let -- Star signals recursive occurrences of the inductive type. See CICwf.TypeChecking.Inductive
      replStage s = if s == I.Star then I.Stage (I.StageVar stage 0) else s
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = I.Stage (I.StageVar stage 0) -- was 1
          coDom = mkApp (Ind indStage True indName (map Bound (reverse [numArgs..numArgs+numPars-1])))  indices
          resType = foldr subst (mkPi (replFunc targs) coDom) pars'
      traceTCM 20 $ vcat [ text "constructor TYPE:" <+> prettyTCM resType ]
      -- We erase the type annotations of both parameters and arguments
      return (Constr x (indName, idConstr) ({- eraseSize -} pars'),
              resType)

--     _  -> __IMPOSSIBLE__

infer (A.Fix f _) = forbidAnnot $ do
  (f', tp, _) <- inferFix f -- inferNoTerm f
  case tp of
    Subset i a t -> do
      alpha <- freshStage (range f)
      addWfConstraint (hat (mkAnnot alpha)) a
      let t' = substSizeName i (mkAnnot alpha) t
      w' <- whnf t'
      return (Fix f' False (mkAnnot alpha), w')
    _            -> __IMPOSSIBLE__

infer (A.Case c) = forbidAnnot $ inferCase c

-- Well-founded sizes
infer (A.Intro rg Nothing e) = do
  (t, u) <- infer e
  -- TODO: check that it is an inductive type (not coinductive)
  -- traceTCM 1 $ text "infer intro" <+> prettyTCM t <+> text "of type" <+> prettyTCM u
  (a, u') <- case unApp u of
    (Ind a True x ps, args) -> return (a, mkApp (Ind (hat a) False x ps) args)
    _ -> typeError rg $ GenericError ("in applied to non-inductive type ("++show u++")")
  return (I.Intro a t, u')

infer (A.CoIntro rg mim Nothing e) = do
  oldSizeMap <- getSizeMap

  im <- getSizeName mim -- freshSizeName (mkName "i")
  stage <- freshStage rg
  (t, u) <- pushWfDecl im (mkAnnot stage) $ infer e
  -- TODO: check that it is a coinductive type (not inductive)
  (a, u') <- case u of
    Ind a True x ps -> return (a, Ind (mkAnnot stage) False x ps)
    _ -> typeError rg $ GenericError "in applied to non-inductive type."
  pushWfDecl im (mkAnnot stage) $ addWfConstraint a (mkAnnot stage)
  pushWfDecl im (mkAnnot stage) $ addWfConstraint (mkAnnot stage) a
  traceTCM 30 $ text "Adding independent" <+> prettyTCM im <+> text "∉" <+> prettyTCM (listAnnot t) $$ text "FROM:" <+> prettyTCM t
  addWfIndependent im (listAnnot t)

  setSizeMap oldSizeMap
  return (I.CoIntro im (mkAnnot stage) t, u')
  where
    getSizeName :: (MonadTCM tcm) => Maybe A.SizeName -> tcm Name
    getSizeName Nothing = freshSizeName (mkName "i")
    getSizeName (Just im) = do
      alpha <- freshSizeName im
      addSize im (mkAnnot alpha)
      return alpha

infer (A.SizeApp rg (A.Local _ x) (Just s)) = do
  (n, b) <- localGetByName x
  traceTCM 35 $ vcat [ text "infer Bound" <+> prettyTCM n
                     , text "in ctx   " <+> (ask >>= prettyTCM) ]
  w <- whnf (I.lift (n + 1) 0 (unArg (bindType b)))
  case w of
    Subset i a t -> do
      sta <- inferSizeApp s
      addWfConstraint (hat sta) a
      let t' = substSizeName i sta t
      w' <- whnf t'
      return (CBound n sta, w')
    _            -> typeError rg $ GenericError "Size application does not have constrained type"
  where
    inferSizeApp :: (MonadTCM tcm) => A.SizeExpr -> tcm Annot
    inferSizeApp A.SizeInfty = return infty
    inferSizeApp (A.SizeExpr rg nm k) = do
      Just annot <- getSize nm
      return $ hatn k annot


infer (A.SizeApp rg (A.Global _ ident) (Just s)) = do
  gl <- getGlobal ident
  let UnConstrType tp = case gl of
        Definition {} -> defType gl
        Assumption {} -> assumeType gl
        Cofixpoint {} -> cofixType gl
        _             -> __IMPOSSIBLE__
  case tp of
    Subset i a t -> do
      sta <- inferSizeApp s
      addWfConstraint (hat sta) a
      let t' = substSizeName i sta t
      w' <- whnf t'
      return (CVar ident sta, w')
    _            -> typeError rg $ GenericError "Size application does not have constrained type"
  where
    inferSizeApp :: (MonadTCM tcm) => A.SizeExpr -> tcm Annot
    inferSizeApp A.SizeInfty = return infty
    inferSizeApp (A.SizeExpr rg nm k) = do
      Just annot <- getSize nm
      return $ hatn k annot


infer e = traceTCM 0 (text ("TODO INFER:") <+> prettyTCM e) >>  __IMPOSSIBLE__


inferConstr stage rg x pars = do
  t <- getGlobal x
  let -- Star signals recursive occurrences of the inductive type. See CICwf.TypeChecking.Inductive
      replStage s = if s == I.Star then stage else s
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = stage
          coDom = mkApp (Ind indStage True indName (map Bound (reverse [numArgs..numArgs+numPars-1])))  indices
          resType = foldr subst (mkPi (replFunc targs) coDom) pars'
      traceTCM 20 $ vcat [ text "constructor TYPE:" <+> prettyTCM resType ]
      -- We erase the type annotations of both parameters and arguments
      return (Constr x (indName, idConstr) pars',
              resType)



check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term
check (A.Meta _ Nothing) u = do
  m <- fresh
  e <- ask
  addGoal m (mkGoal e u)
  return (Meta m)

check (A.Intro rg Nothing e) (Ind a False x pars) = do
  a' <- unHat a
  e' <- check e (Ind a' True x pars)
  return $ Intro a' e'
    where
      unHat (Stage Infty) = return infty
      unHat (Stage (StageVar k n)) | n > 0 = return (Stage (StageVar k (n-1)))
      unHat (SizeVar x n) | n > 0 = return (SizeVar x (n-1))
      unHat a = do
        stage <- freshStage rg
        addWfConstraint (hat (mkAnnot stage)) a
        return (mkAnnot stage)

check e@(A.Constr rg _ _) i@(Ind a False x pars) = do
  g@(Inductive {}) <- getGlobal x
  case indKind g of
    I -> check (A.Intro rg Nothing e) i
    CoI -> check (A.CoIntro rg Nothing Nothing e) i

check (A.CoIntro rg Nothing Nothing e) (Ind a False x pars) = do
  im <- freshSizeName (mkName "i")
  e' <- pushWfDecl im a $ check e (Ind (mkAnnot im) True x pars)
  traceTCM 30 $ text "Adding independent" <+> prettyTCM im <+> text "_|_" <+> prettyTCM (listAnnot e') $$ text "FROM:" <+> prettyTCM e' $$ text "RAW:" <+> text (show e')
  addWfIndependent im (listAnnot e')
  return (I.CoIntro im a e')

check (A.CoIntro rg mim Nothing e) (Ind a False x pars) = do
  oldSizeMap <- getSizeMap

  im <- getSizeName mim -- freshSizeName (mkName "i")
  e' <- pushWfDecl im a $ check e (Ind (mkAnnot im) True x pars)
  traceTCM 30 $ text "Adding independent" <+> prettyTCM im <+> text "_|_" <+> prettyTCM (listAnnot e') $$ text "FROM:" <+> prettyTCM e' $$ text "RAW:" <+> text (show e')
  addWfIndependent im (listAnnot e')
  setSizeMap oldSizeMap
  return (I.CoIntro im a e')

  where
    getSizeName :: (MonadTCM tcm) => Maybe A.SizeName -> tcm Name
    getSizeName Nothing = freshSizeName (mkName "i")
    getSizeName (Just im) = do
      alpha <- freshSizeName im
      addSize im (mkAnnot alpha)
      return alpha


check e i@(Ind a True _ _) | (A.Constr rg x pars, args) <- A.unApp e = do
  (c, t) <- inferConstr a rg x pars
  (args', t') <- checkArgs args t
  unlessM (t' `subType` i) $ typeError (range e) $ NotConvertible t' i
  return (mkApp c args')
  where
    checkArgs :: (MonadTCM tcm) => [A.Expr] -> Type -> tcm ([Term], Type)
    checkArgs [] t = return ([], t)
    checkArgs (e:es) (Pi ctx u) = do
      let (ch, ct) = ctxSplit ctx
      t2 <- forbidAnnot $ check e (unArg (bindType ch))
      w  <- whnf $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u)
      (ts, w') <- checkArgs es w
      return (t2 : ts, w')

check t u = do
  traceTCM 35 $ hsep [ text "Checking type of", prettyTCM t
                     , text "against", prettyTCM u]
  wfSetCheckpoint
  traceTCM 35 $ text "SET CHECKPOINT"
  (t', r) <- infer t
  traceTCM 35 $ hsep [text "Calling subtype with ", prettyTCM r,
                      text "≤", prettyTCM u]
  traceTCM 35 $ hsep [text "Calling subtype with ", text (show r),
                      text "≤", text (show u)]
  b <- r `subType` u
  -- If conversion fails, try inserting a coercion
  if b
    then traceTCM 35 (text "REMOVE CHECKPOINT") >> wfDelCheckpoint >> return t'
    else do
    r1 <- normalForm r
    u1 <- normalForm u
    case (unApp r1, unApp u1) of
      ((Ind a1 True  x1 ps1, args1),
       (Ind a2 False x2 ps2, args2)) | x1 == x2 -> do
        g@(Inductive {}) <- getGlobal x1
        case indKind g of
          I -> do
            stage <- freshStage (range t)
            addWfConstraint (mkAnnot stage) infty
            addWfConstraint (hat a1) (mkAnnot stage)
            b1 <- mkApp (Ind (mkAnnot stage) False x1 ps1) args1
                  `subType` mkApp (Ind a2 False x2 ps2) args2
            unless b1 $ typeError (range t) $ NotConvertible r u
            traceTCM 35 (text "REMOVE CHECKPOINT")
            wfDelCheckpoint
            return (I.Intro a1 t')

          -- CoI -> do
          --   -- TODO: push im <= stage to all constraints generated from t
          --   im <- freshSizeName (mkName "i")
          --   stage <- freshStage (range t)
          --   b1 <- mkApp (Ind (mkAnnot stage) False x1 ps1) args1
          --         `subType` mkApp (Ind a2 False x2 ps2) args2
          --   unless b1 $ typeError (range t) $ NotConvertible r u
          --   traceTCM 20 $ text "Ammending constraints:"
          --     <+> (getWfConstraints >>= prettyTCM)
          --   wfAddDecl im (mkAnnot stage)
          --   traceTCM 20 $ text "Fixed constraints:"
          --     <+> (getWfConstraints >>= prettyTCM)
          --   -- addWfConstraint (mkAnnot stage) infty
          --   pushWfDecl im (mkAnnot stage) $ addWfConstraint (mkAnnot im) a1
          --   pushWfDecl im (mkAnnot stage) $ addWfConstraint a1 (mkAnnot im)
          --   addWfIndependent im (listAnnot t')
          --   return (I.CoIntro im a1 t')
          _ -> typeError (range t) $ NotConvertible r u

      _ -> typeError (range t) $ NotConvertible r u

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


inferConstrType :: (MonadTCM tcm) => A.ConstrExpr -> tcm (ConstrType, Sort)
inferConstrType (A.UnConstrExpr e) = do
  (tp, s) <- inferType e
  return (UnConstrType tp, s)

inferConstrType (A.ConstrExpr rg i e) = do
  a <- freshSizeName i
  addSize i (mkAnnot a)
  let pushConstr = pushWfDecl a infty
  (tp, s) <- pushConstr $ inferType e
  let r = ConstrType a tp
  -- traceTCM 1 $ hsep [ text "Inferred:"
  --                   , prettyTCM r
  --                   , text "from:"
  --                   , prettyTCM (A.ConstrExpr rg s1 s2 e) ]
  return (r, s)
