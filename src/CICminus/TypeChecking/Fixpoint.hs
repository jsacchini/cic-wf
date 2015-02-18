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

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module CICminus.TypeChecking.Fixpoint where

import           CICminus.Utils.Impossible

import           Control.Monad.Reader

import           Data.List
import           Data.Maybe

import qualified CICminus.Syntax.Abstract           as A
import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal           as I
import           CICminus.Syntax.Position
-- import           CICminus.Syntax.Size

import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.Constraints
import           CICminus.TypeChecking.Whnf
import           CICminus.TypeChecking.PrettyTCM    hiding ((<>))
import           CICminus.TypeChecking.RecCheck
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.TCMErrors
import {-# SOURCE #-} CICminus.TypeChecking.TypeChecking
import CICminus.Utils.Sized

extractIndType :: (MonadTCM tcm) => Type
                  -> tcm (Name, InductiveKind, StageVar, [Term])
extractIndType tp = do
  (annot, nm, args) <-
    case tp of
      App (Ind a n ps) ts -> return (a, n, ps ++ ts)
      Ind a n ps          -> return (a, n, ps)
      _                   -> notImplemented noRange ("Recursive argument not inductive" ++ show tp)
  i <- getGlobal nm -- must be (co-)inductive
  return (nm, indKind i, fromJust (sbase annot), args)



-- | checkCoFixpointBody 'f' 'T' 'G' 'U' 't' check the following judgment:
--  (f:T) G |- t : U    (G and U need to be lifted to account for f.
checkCoFixpointBody :: (MonadTCM tcm) => Name -> Type -> Context -> Type
                       -> A.Expr
                       -> tcm Term
checkCoFixpointBody f tpRec ctx tpRet body = do
  let ctx1   = lift0 1 ctx
      tpRet1 = I.lift 1 (size ctx) tpRet

  pushBind (mkBind f tpRec)
    $ pushCtx ctx1
    $ traceTCM 20 (text "Checking body:" <+> prettyTCM body
                   $$ text "against" <+> prettyTCM tpRet1
                   $$ text "in ctx" <+> (ask >>= prettyTCM) )

  body' <- forbidAnnot $ pushBind (mkBind f tpRec)
           $ pushCtx ctx1 $ check body tpRet1

  pushBind (mkBind f tpRec)
    $ pushCtx ctx1
    $ traceTCM 20 (text "Typechecked body" <+> prettyTCM body'
                   $$ text "against" <+> prettyTCM tpRet1
                   $$ text "in ctx" <+> (ask >>= prettyTCM)
                   $$ text "-------")

  return body'


admissibilityRecusrion :: (MonadTCM tcm) => Range ->
                          Int -> FixSpec -> Context -> Type
                          -> tcm (StageVar, [StageVar], Context, Type)
admissibilityRecusrion rg nRec spec ctx tpRet = do
  let (ctx0, recArg :> ctx1) = ctxSplitAt nRec ctx

  (_, iKind, alpha, args) <- extractIndType (unArg (bindType recArg))
  when (iKind /= I) $ error "recursive type is coinductive"

  case spec of
    FixPosition -> do
      recpos <- getStarStageVar
      -- Check that args have no star annotations
      let argsVars = mapMaybe sbase $ listAnnot args
          commonVars = intersect recpos argsVars
      unless (null commonVars) $ notImplemented rg "Star in arguments of recursive argument"

      -- Enforce star stages to occur positively in Pi ctx1 tp
      let shiftStar s@(Stage (StageVar x _)) | x `elem` recpos = hat s
                                             | otherwise = s
          shiftStar s = s
          recArgn = modifySize shiftStar recArg
          ctx1n = modifySize shiftStar ctx1
          tpn   = modifySize shiftStar tpRet

      traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)

      -- Add Constraints to ensure that alpha appears positively in the return type
      pushCtx ctx0 $ traceTCM 20
        $ hsep [ text "Subtype: "
               , prettyTCM (mkPi (recArg:>ctx1) tpRet)
               , text "<="
               , prettyTCM (mkPi (recArgn:>ctx1n) tpn) ]
      _ <- pushCtx (ctxPush ctx0 recArg)
           $ subType (mkPi ctx1 tpRet) (mkPi ctx1n tpn)

      return (alpha, recpos, ctxCat ctx0 (recArgn :> ctx1n), tpn)

    FixStage stage -> do
      -- Check that args have no star annotations
      let argsVars = mapMaybe nbase $ listAnnot args
      unless (null argsVars) $ notImplemented rg "annotations in arguments of recursive argument"

      -- Enforce annotated stages to occur positively in Pi ctx1 tp
      let shiftAlpha s@(SizeVar v _) | v == stage = hat s
          shiftAlpha s = s
          recArgn = modifySize shiftAlpha recArg
          ctx1n = modifySize shiftAlpha ctx1
          tpn   = modifySize shiftAlpha tpRet

      traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)

      -- Add Constraints to ensure that alpha appears positively in the
      -- return type
      pushCtx ctx0 $ traceTCM 20
        $ hsep [ text "Subtype: "
               , prettyTCM (mkPi ctx1 tpRet)
               , text "<="
               , prettyTCM (mkPi ctx1n tpn) ]
      _ <- pushCtx (ctxPush ctx0 recArg)
           $ subType (mkPi ctx1 tpRet) (mkPi ctx1n tpn)

      return (alpha, [alpha], ctxCat ctx0 (recArgn :> ctx1n), tpn)

    FixStruct -> do
      posOcc <- findOccurrences POS (mkPi ctx1 tpRet)

      traceTCM 20 $ (text "In TYPE:" <+> prettyTCM (mkPi ctx1 tpRet)
                     $$ text "POS: " <+> prettyTCM posOcc)
      -- Create new stages for each possibe positive
      currConstr <- allConstraints
      succPos <- mapM (\x -> freshStage (fromJust (lab (unSC currConstr) (VarNode x))) >>= \sta -> return (x, sta)) posOcc
      traceTCM 20 $ (text "NEW STAGES:" <+> prettyTCM succPos)

      -- Enforce annotated stages to occur positively in Pi ctx1 tp
      let shiftAlpha s@(Stage (StageVar v _)) | v == alpha = hat s
          shiftAlpha s@(Stage (StageVar v _)) =
            case lookup v succPos of
              Just sta -> Stage (StageVar sta 0)
              Nothing -> s
          shiftAlpha s = s
          recArgn = modifySize shiftAlpha recArg
          ctx1n = modifySize shiftAlpha ctx1
          tpn   = modifySize shiftAlpha tpRet

      traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)

      return (alpha, [], ctxCat ctx0 (recArgn :> ctx1n), tpn)



-- | checkAdmissibility 'ki' 'n' 'ctx' 'tp'
--
--   Check that type 'Pi ctx tp' is admissible for recursion using 'ki', where
--   'n' is the index of the recursive argument (ignored if 'ki' is 'CoI')
--   Return the recursive size, and the next type
checkAdmissibility :: (MonadTCM tcm) => Range ->
                      InductiveKind -> Int -> Context -> Type
                      -> tcm (StageVar, Context, Type)
checkAdmissibility rg I nRec ctx tp = do
  let (ctx0, recArg :> ctx1) = ctxSplitAt nRec ctx
  starVars <- getStarStageVar

  (_, iKind, alpha, args) <- extractIndType (unArg (bindType recArg))
  when (iKind /= I) $ error "recursive type is coinductive"

  -- Check that args have no star annotations
  let argsVars = mapMaybe sbase $ listAnnot args
      commonVars = intersect starVars argsVars
  unless (null commonVars) $ notImplemented rg "Star in arguments of recursive argument"

  -- Enforce star stages to occur positively in Pi ctx1 tp
  let shiftStar s@(Stage (StageVar x _)) | x `elem` starVars = hat s
                                         | otherwise = s
      shiftStar s = s
      recArgn = modifySize shiftStar recArg
      ctx1n = modifySize shiftStar ctx1
      tpn   = modifySize shiftStar tp

  traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)

  -- Add Constraints to ensure that alpha appears positively in the return type
  pushCtx ctx0 $ traceTCM 20
    $ hsep [ text "Subtype: "
           , prettyTCM (mkPi (recArg:>ctx1) tp)
           , text "<="
           , prettyTCM (mkPi (recArgn:>ctx1n) tpn) ]
  _ <- pushCtx (ctxPush ctx0 recArg)
       $ subType (mkPi ctx1 tp) (mkPi ctx1n tpn)

  return (alpha, ctxCat ctx0 (recArgn :> ctx1n), tpn)


checkAdmissibility rg CoI _ ctx tp = do
  starVars <- getStarStageVar

  (_, iKind, alpha, args) <- extractIndType tp
  when (iKind /= CoI) $ error "return type is inductive"

  -- Check that args have no star annotations
  let argsVars = mapMaybe sbase $ listAnnot args
      commonVars = intersect starVars argsVars
  unless (null commonVars) $ notImplemented rg "Star in arguments of recursive argument"

  -- Enforce star stages to occur negatively ctx
  let shiftStar s@(Stage (StageVar x _)) | x `elem` starVars = hat s
                                         | otherwise = s
      shiftStar s = s
      ctxn = modifySize shiftStar ctx
      tpn  = modifySize shiftStar tp

  traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi ctxn tpn)

  -- Add Constraints to ensure that alpha appears positively in the return type
  traceTCM 20
    $ hsep [ text "Subtype: "
           , prettyTCM ctxn
           , text "<="
           , prettyTCM ctx ]
  _ <- subType ctxn ctx

  return (alpha, ctxn, tpn)





inferFix :: (MonadTCM tcm) => A.FixExpr -> tcm (FixTerm, Type, ConstrType)
inferFix fixexpr@(A.FixExpr rg ki nmf (A.FixPosition nRec) args tp body) = do

  -- Save star stages
  oldStarStages <- getStarStageVar

  clearStarStageVar
  allOld <- allStages -- all stages before typechecking fix
  traceTCM 20 $ hsep [ text "Typechecking fixpoint type (position): "
                     , prettyTCM args
                     , text ":"
                     , prettyTCM tp ]

  (argCtx, _) <- allowStar $ inferBinds args
  traceTCM 20 $ hsep [ text "Typechecked args"
                     , prettyTCM argCtx ]
  (tp', s) <- allowStar $ pushCtx argCtx $ inferType tp
  traceTCM 20 $ hsep [ text "Typechecked fixpoint type: "
                     , prettyTCM (mkPi argCtx tp')]
  is <- getStarStageVar
  traceTCM 20 $ hsep [ text "Position args: "
                     , prettyTCM is ]

  (alpha, argCtx', retTp) <- checkAdmissibility (fuseRange args tp) ki nRec argCtx tp'

  let recType = mkPi argCtx tp'
  body' <- checkCoFixpointBody nmf (mkPi argCtx tp') argCtx' retTp body

  -- Calling recCheck
  let vNeq = (allOld ++ mapMaybe extractVar (listAnnot recType ++ listAnnot body')) \\ map VarNode is
      extractVar (Stage (StageVar ss _)) = Just (VarNode ss)
      extractVar _ = Nothing
  alls <- allStages
  cOld <- allConstraints
  traceTCM 15 $ (hsep [text "I calling recCheck alpha = ", prettyTCM alpha]
                 $$ nest 2 (vcat [text "vStar =" <+> prettyTCM is,
                                  text "all other =" <+> prettyTCM (alls \\ map VarNode is),
                                  text "vNeq =" <+> prettyTCM vNeq,
                                  text "C =" <+> text (show cOld)]))

  let recRes :: Either SizeConstraint [StageNode]
      recRes = recCheck (VarNode alpha) (map VarNode is) vNeq cOld


  case recRes of
    Left cNew -> do newConstraints cNew
    Right xs  -> do -- traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                    traceTCM 15 $ vcat [ text "FIX FAILED ON CTX" <+> prettyTCM rg
                                       , (ask >>= prettyTCM)
                                       , text "------------------------"
                                       , prettyTCM (A.Fix fixexpr)
                                       , text "============"
                                       , text ("cycle" ++ show xs)]
                    error ("FIX " ++ show xs)


  let (Left recRes') = recRes
  traceTCM 20 $ hsep [ text "result recCheck ", text (show recRes') ]

  -- Find constrained type
  starStages <- getStarStageVar
  allconstr <- allConstraints
  let recStages = starStages
      sps :: [(StageVar, Int)]
      sps = map (\s -> (s, 0 - fromJust (shortestPath (unSC allconstr) (VarNode alpha) (VarNode s)))) recStages
  traceTCM 10 $ (text "Shortest paths to" <+> prettyTCM alpha
                 $$ nest 2 (prettyTCM sps)
                 $$ text ("Constraints: " ++ show allconstr) )

  let cvar = mkName "i"
      sizeToi (Stage (StageVar s _)) =
        case lookup s sps of
          Just k -> SizeVar cvar k
          Nothing -> Stage Infty
      sizeToi _ = Stage Infty

      ctype = ConstrType [cvar] (modifySize sizeToi (mkPi argCtx tp'))

  traceTCM 10 $ (text "Constrained type" <+> prettyTCM ctype)

  -- Restore star stages
  setStarStageVar oldStarStages

  -- Final result
  let toStar (Stage (StageVar s _)) | s `elem` starStages = Star
                                    | otherwise           = Empty
      toStar _ = Empty

  return ( FixTerm ki nRec nmf FixPosition
           (modifySize toStar argCtx) (modifySize toStar tp') body'
         , mkPi argCtx tp'
         , ctype )


------------------------------------------------
-- * fix f <i> Delta : T := t
------------------------------------------------

inferFix fixexpr@(A.FixExpr rg I nmf
                  (A.FixStage rgsta stage nRec) args tp body) = do

  oldSizeMap <- getSizeMap
  allOld <- allStages -- all stages before typechecking fix

  alpha <- freshStage rgsta
  addSize stage alpha

  (argCtx, _) <- allowSizes  $ inferBinds args
  (tp', s) <- allowSizes $ pushCtx argCtx $ inferType tp


  traceTCM 20 $ hsep [ text "Typechecked fixpoint type: "
                     , prettyTCM (mkPi argCtx tp')]


  let (ctx0, recArg :> ctx1) = ctxSplitAt nRec argCtx

  (_, iKind, _, args) <- extractIndType (unArg (bindType recArg))
  when (iKind /= I) $ error "recursive type is coinductive"

  -- Check that args have no star annotations
  let argsVars = mapMaybe nbase $ listAnnot args
  unless (null argsVars) $ notImplemented rg "annotations in arguments of recursive argument"

  -- Enforce annotated stages to occur positively in Pi ctx1 tp
  let shiftAlpha s@(SizeVar _ _) = hat s
      shiftAlpha s = s
      recArgn = modifySize shiftAlpha recArg
      ctx1n = modifySize shiftAlpha ctx1
      tpn   = modifySize shiftAlpha tp'

  traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)

  -- Add Constraints to ensure that alpha appears positively in the return type
  pushCtx ctx0 $ traceTCM 20
    $ hsep [ text "Subtype: "
           , prettyTCM (mkPi ctx1 tp')
           , text "<="
           , prettyTCM (mkPi ctx1n tpn) ]
  _ <- pushCtx (ctxPush ctx0 recArg)
       $ subType (mkPi ctx1 tp') (mkPi ctx1n tpn)

  let argCtx' = ctxCat ctx0 (recArgn :> ctx1n)
      recType = mkPi argCtx tp'

  body' <- checkCoFixpointBody nmf recType argCtx' tpn body


  -- Calling recCheck
  let vNeq = (allOld ++ mapMaybe extractVar (listAnnot recType ++ listAnnot body'))
      extractVar (Stage (StageVar ss _)) = Just (VarNode ss)
      extractVar _ = Nothing
  alls <- allStages
  cOld <- allConstraints
  traceTCM 15 $ (hsep [text "I calling recCheck alpha = ", prettyTCM alpha]
                 $$ nest 2 (vcat [text "all other =" <+> prettyTCM (alls \\ [VarNode alpha]),
                                  text "vNeq =" <+> prettyTCM vNeq,
                                  text "C =" <+> text (show cOld)]))

  let recRes :: Either SizeConstraint [StageNode]
      recRes = recCheck (VarNode alpha) [VarNode alpha] vNeq cOld


  case recRes of
    Left cNew -> do newConstraints cNew
    Right xs  -> do -- traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                    traceTCM 15 $ vcat [ text "FIX FAILED ON CTX" <+> prettyTCM rg
                                       , (ask >>= prettyTCM)
                                       , text "------------------------"
                                       , prettyTCM (A.Fix fixexpr)
                                       , text "============"
                                       , text ("cycle" ++ show xs)]
                    error ("FIX " ++ show xs)


  let (Left recRes') = recRes
  traceTCM 20 $ hsep [ text "result recCheck ", text (show recRes') ]

  -- Find constrained type
  let eraseNotAlpha _ s@(SizeVar _ _) = s
      eraseNotAlpha r _ = r

      ctype = ConstrType [stage] (modifySize (eraseNotAlpha (Stage Infty)) (mkPi argCtx tp'))

  traceTCM 10 $ (text "Constrained type" <+> prettyTCM ctype)
  traceTCM 10 $ (text "Erased constrained type" <+> prettyTCM (mkPi (modifySize (eraseNotAlpha Empty) argCtx) (modifySize (eraseNotAlpha Empty) tp')))

  -- Restore star stages
  setSizeMap oldSizeMap

  -- Final result
  return ( FixTerm I nRec nmf (FixStage stage)
           (modifySize (eraseNotAlpha Empty) argCtx) (modifySize (eraseNotAlpha Empty) tp')
           (eraseSize body')
         , mkPi argCtx tp'
         , ctype )



------------------------------------------------
-- * fix f Delta { struct x } : T := t
------------------------------------------------

inferFix fixexpr@(A.FixExpr rg I nmf
                  (A.FixStruct rgspec nRec) args tp body) = do

  allOld <- allStages -- all stages before typechecking fix

  (argCtx, _) <- forbidAnnot  $ inferBinds args
  (tp', s) <- forbidAnnot $ pushCtx argCtx $ inferType tp


  traceTCM 20 $ hsep [ text "Typechecked fixpoint type: "
                     , prettyTCM (mkPi argCtx tp')]


  let (ctx0, recArg :> ctx1) = ctxSplitAt nRec argCtx

  (_, iKind, alpha, args) <- extractIndType (unArg (bindType recArg))
  when (iKind /= I) $ error "recursive type is coinductive"

  posOcc <- pushCtx (ctxPush ctx0 recArg) $ findOccurrences POS (mkPi ctx1 tp')

  traceTCM 20 $ (text "In TYPE:" <+> prettyTCM (mkPi ctx1 tp')
                 $$ text "POS: " <+> prettyTCM posOcc)
  -- Create new stages for each possibe positive
  currConstr <- allConstraints
  succPos <- mapM (\x -> freshStage (fromJust (lab (unSC currConstr) (VarNode x))) >>= \sta -> return (x, sta)) posOcc
  traceTCM 20 $ (text "NEW STAGES:" <+> prettyTCM succPos)



  -- Enforce annotated stages to occur positively in Pi ctx1 tp
  let shiftAlpha s@(Stage (StageVar v _)) | v == alpha = hat s
      shiftAlpha s@(Stage (StageVar v _)) =
        case lookup v succPos of
          Just sta -> Stage (StageVar sta 0)
          Nothing -> s
      shiftAlpha s = s
      recArgn = modifySize shiftAlpha recArg
      ctx1n = modifySize shiftAlpha ctx1
      tpn   = modifySize shiftAlpha tp'

  traceTCM 20 $ text "Return Type:" <+> prettyTCM (mkPi (ctxCat ctx0 (recArgn :> ctx1n)) tpn)


  let argCtx' = ctxCat ctx0 (recArgn :> ctx1n)
      recType = mkPi argCtx tp'

  body' <- checkCoFixpointBody nmf recType argCtx' tpn body


  -- Calling recCheck
  let vNeq = (allOld ++ mapMaybe extractVar (listAnnot recType ++ listAnnot body')) \\ (map VarNode (alpha : posOcc))
      extractVar (Stage (StageVar ss _)) = Just (VarNode ss)
      extractVar _ = Nothing
  alls <- allStages
  cOld <- allConstraints
  traceTCM 15 $ (hsep [text "I calling recCheck alpha = ", prettyTCM alpha]
                 $$ nest 2 (vcat [text "all other =" <+> prettyTCM (alls \\ [VarNode alpha]),
                                  text "vNeq =" <+> prettyTCM vNeq,
                                  text "C =" <+> text (show cOld)]))

  let recRes :: Either SizeConstraint [StageNode]
      recRes = recCheck (VarNode alpha) [VarNode alpha] vNeq cOld


  case recRes of
    Left cNew -> do newConstraints cNew
    Right xs  -> do -- traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                    traceTCM 15 $ vcat [ text "FIX FAILED ON CTX" <+> prettyTCM rg
                                       , (ask >>= prettyTCM)
                                       , text "------------------------"
                                       , prettyTCM (A.Fix fixexpr)
                                       , text "============"
                                       , text ("cycle" ++ show xs)]
                    error ("FIX " ++ show xs)


  let (Left recRes') = recRes
  traceTCM 20 $ hsep [ text "result recCheck ", text (show recRes') ]

  -- Find possible recursive stages
  cNew <- allConstraints
  let neqUp = upward (unSC cNew) (InftyNode : vNeq)
      leftPos = filter (\(x, sx) -> not (VarNode x `elem` neqUp) && not (VarNode sx `elem` neqUp)) succPos
  traceTCM 20 $ hsep [ text "vNeq upward ", text (show neqUp) ]
  traceTCM 20 $ hsep [ text "possible rec", text (show leftPos) ]

  newPos <- filterM (isRecursive (VarNode alpha) (InftyNode : vNeq)) (map (\(x,y) -> (VarNode x, VarNode y)) succPos)

  traceTCM 20 $ hsep [ text "Found positive", text (show newPos) ]
  traceTCM 20 $ hsep [ text "New constraints", allConstraints >>= \constr -> text (show constr) ]

  -- Find constrained type
  allconstr <- allConstraints
  let recStages = map fst newPos
      sps :: [(StageNode, Int)]
      sps = map (\s -> (s, 0 - fromJust (shortestPath (unSC allconstr) (VarNode alpha) s))) recStages
  traceTCM 10 $ (text "Shortest paths to" <+> prettyTCM alpha
                 $$ nest 2 (prettyTCM sps)
                 $$ text ("Constraints: " ++ show allconstr) )

  let cvar = mkName "i"
      sizeToi (Stage (StageVar s _)) =
        case lookup (VarNode s) ((VarNode alpha, 0) : sps) of
          Just k -> SizeVar cvar k
          Nothing -> Stage Infty
      sizeToi _ = Stage Infty

      ctype = ConstrType [cvar] (modifySize sizeToi (mkPi argCtx tp'))

  traceTCM 10 $ (text "Constrained type" <+> prettyTCM ctype)


  -- Final result
  return ( FixTerm I nRec nmf FixStruct
           (eraseSize argCtx) (eraseSize tp')
           (eraseSize body')
         , mkPi argCtx tp'
         , ctype )

    where
      isRecursive :: (MonadTCM tcm) => StageNode -> [StageNode]
                     -> (StageNode, StageNode) -> tcm Bool
      isRecursive alpha vNeq (stage, succStage) = do
        old <- allConstraints
        addStageConstraints [(stage, succStage, -1), (succStage, stage, 1)]
        let down = downward (unSC old) [stage, succStage]
        forM_ down (\x -> addStageConstraints [(alpha, x, 0)])
        constr <- allConstraints
        case findNegCycle succStage (unSC constr) of
          [] -> do
            let upNeq = upward (unSC constr) vNeq
            if stage `elem` upNeq
              then newConstraints old >> return False
              else return True
          _ -> newConstraints old >> return False


data OCC = NEG | POS | NEUT
         deriving(Eq, Show)

opposite :: OCC -> OCC
opposite NEG = POS
opposite POS = NEG
opposite NEUT = NEUT

compose :: OCC -> OCC -> OCC
compose NEG o = opposite o
compose o NEG = opposite o
compose NEUT o = o
compose o NEUT = o
compose POS POS = POS

occ :: Polarity -> OCC
occ Neg = NEG
occ Neut = NEUT
occ _ = POS

occKind :: OCC -> InductiveKind -> Bool
occKind POS I   = True
occKind NEG CoI = True
occKind _   _   = False



findOccurrences :: (MonadTCM tcm) => OCC -> Type -> tcm [I.StageVar]
findOccurrences o tp = do
  wh <- whnf tp
  case unApp wh of
    (Ind a nm pars, args) -> do
      g <- getGlobal nm
      case g of
        ind@Inductive {}
          | occKind o (indKind ind) -> do
            s1 <- mapM (\(pol, p) -> findOccurrences (compose o (occ pol)) p)
                  (zip (indPol ind) pars)
            let s2 = catMaybes [sbase a]
            return $ concat s1 ++ s2
          | otherwise -> return []
          -- TODO: occ in pars
    (Pi ctx tp', []) -> do
      s1 <- findOccurrencesCtx (opposite o) ctx
      s2 <- pushCtx ctx $ findOccurrences o tp'
      return $ s1 ++ s2
    _ -> return []

findOccurrencesCtx :: (MonadTCM tcm) => OCC -> Context -> tcm [I.StageVar]
findOccurrencesCtx _ CtxEmpty = return []
findOccurrencesCtx o (b :> ctx) = do
  s1 <- findOccurrences o (unArg (bindType b))
  s2 <- pushBind b $ findOccurrencesCtx o ctx
  return $ s1 ++ s2



----------------------------------------
-- fix f Δ* : T* := t
----------------------------------------

-- inferFixPosition :: (MonadTCM tcm) => Range -> Name -> Int -> A.Context
--                     -> A.Expr -> A.Expr -> tcm (FixTerm, Type, ConstrType)
-- inferFixPosition rg fix recarg ctx tp body = do
