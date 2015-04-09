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

module CICwf.TypeChecking.Fixpoint where

import           CICwf.Utils.Impossible

import           Control.Monad.Reader

import           Data.List
import           Data.Maybe
import           Data.Set            (Set)
import qualified Data.Set            as Set

import qualified CICwf.Syntax.Abstract           as A
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           as I
import           CICwf.Syntax.Position
-- import           CICwf.Syntax.Size

import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.Constraints
import           CICwf.TypeChecking.Whnf
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import           CICwf.TypeChecking.RecCheck
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors
import {-# SOURCE #-} CICwf.TypeChecking.TypeChecking
import CICwf.Utils.Sized

extractIndType :: (MonadTCM tcm) => Type
                  -> tcm (Name, InductiveKind, StageVar, [Term])
extractIndType tp = do
  (annot, nm, args) <-
    case tp of
      App (Ind a _ n ps) ts -> return (a, n, ps ++ ts)
      Ind a _ n ps          -> return (a, n, ps)
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
inferFix fixexpr@(A.FixExpr rg ki nmf (A.FixPosition nRec) args tp body) =
  typeError rg $ GenericError "Position types are not allowed."

inferFix fixexpr@(A.FixExpr rg I nmf
                  (A.FixStruct rgspec nRec) args tp body) =
  typeError rg $ GenericError "Structural recursion is not allowed."

------------------------------------------------
-- * fix f <i> Delta : T := t
------------------------------------------------

inferFix fixexpr@(A.FixExpr rg ki nmf
                  (A.FixStage rgsta stage nRec) args tp body) = do

  oldSizeMap <- getSizeMap
  allOld <- allStages -- all stages before typechecking fix

  alpha <- freshSizeName stage
  addSize stage (mkAnnot alpha)


  (argCtx, _) <- allowSizes $ pushWfDecl alpha infty $ inferBinds args
  (tp', s) <- allowSizes $ pushWfDecl alpha infty $ pushCtx argCtx $ inferType tp


  traceTCM 20 $ hsep [ text "Typechecked fixpoint type: "
                     , prettyTCM (mkPi argCtx tp')]

  let resType = subsetType alpha infty (mkPi argCtx tp')
  traceTCM 20 $ hsep [ text "Well-founded fixpoint type: "
                     , prettyTCM resType ]


  let argsAnnot = Set.delete (mkAnnot alpha) (fAnnot (mkPi argCtx tp'))
  addWfIndependent alpha (Set.elems argsAnnot)

  -- let (ctx0, recArg :> ctx1) = ctxSplitAt nRec argCtx

  -- (_, iKind, _, args) <- extractIndType (unArg (bindType recArg))
  -- when (iKind /= I) $ error "recursive type is coinductive"

  -- Check that args have no star annotations
  -- let argsVars = mapMaybe nbase $ listAnnot args
  -- unless (null argsVars) $ notImplemented rg "annotations in arguments of recursive argument"

  -- Well-founded return type
  let replRecStage jm s@(SizeVar im n) | alpha == im = hatn n (mkAnnot jm)
      replRecStage _  s                              = s

  jm <- freshSizeName (mkName "j")
  let wfret = modifySize (replRecStage jm) (mkPi argCtx tp')
      recType = subsetType jm (mkAnnot alpha) wfret
  traceTCM 20 $ hsep [ text "Well-founded return type: "
                     , prettyTCM recType ]

  body' <- pushWfDecl alpha infty $ checkCoFixpointBody nmf recType argCtx tp' body

  addWfIndependent alpha (Set.elems (fAnnot body'))


  -- Find constrained type
  let eraseNotAlpha _ s = s
      -- eraseNotAlpha _ s@(SizeVar _ _) = s
      -- eraseNotAlpha r _ = r

      ctype = ConstrType [stage] (modifySize (eraseNotAlpha (Stage Infty)) (mkPi argCtx tp'))

  traceTCM 10 $ (text "Constrained type" <+> prettyTCM ctype)
  traceTCM 10 $ (text "Erased constrained type" <+> prettyTCM (mkPi (modifySize (eraseNotAlpha Empty) argCtx) (modifySize (eraseNotAlpha Empty) tp')))

  -- Restore star stages
  setSizeMap oldSizeMap

  -- Final result
  return ( FixTerm ki nRec nmf (FixStage alpha)
           (modifySize (eraseNotAlpha Empty) argCtx) (modifySize (eraseNotAlpha Empty) tp')
           ({- eraseSize -} body')
         , resType -- mkPi argCtx tp'
         , ConstrType [] resType )-- ctype )





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
    (Ind a _ nm pars, args) -> do
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
