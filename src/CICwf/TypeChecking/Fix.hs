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

module CICwf.TypeChecking.Fix where

#include "undefined.h"
import           CICwf.Utils.Impossible

import           Control.Monad.Reader

import           Data.List
import           Data.Maybe
import           Data.Monoid

import qualified CICwf.Syntax.Abstract           as A
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           as I
import           CICwf.Syntax.InternalToAbstract
import           CICwf.Syntax.Position
-- import           CICwf.Syntax.Size

import           CICwf.TypeChecking.Constraints
import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import qualified CICwf.TypeChecking.PrettyTCM    as PP ((<>))
import           CICwf.TypeChecking.RecCheck
import           CICwf.TypeChecking.TCM
import {-# SOURCE #-} CICwf.TypeChecking.TypeChecking
import           CICwf.TypeChecking.Whnf

import           CICwf.Utils.Pretty
import           CICwf.Utils.Sized


-- | 'collectStars' @e@ @t@ assumes that @e@ and @t@ have the same shape
--   Returns the list of stage variables occuring in @t@ whose corresponding
--   position in @e@ has a star.
--   @t@ is the typed version of @e@ so they should have the same shape.
--   For now, we assume that @e@ and @t@ are "simple" types, so star occur in
--   (co-)inductive types directly under products.
collectStars :: (MonadTCM tcm) => A.Expr -> Type -> tcm [I.StageVar]
collectStars e t =
  do
    rs2 <- collectStarsNonPi e' t'
    rs1 <- collectStarsBind ctx1 ctx2
    return $ rs1 ++ rs2
  where
    (ctx1, e'_ ) = A.unPi e
    (ctx2, t') = unPi t

                 -- collectStars e                 (Pi ctx t2) | ctxIsNull ctx = collectStars e t2
collectStarsNonPi :: (MonadTCM tcm) => A.Expr -> Type -> tcm [I.StageVar]
-- collectStars (A.Arrow _ e1 e2) (Pi ctx t2) =
--   do
--     rs2 <- collectStars e2 (mkPi ctx' t2)
--     rs1 <- collectStars (implicitValue e1) (bindType b1)
--     return $  rs1 ++ rs2
--   where
--     (b1, ctx') = ctxSplit ctx
collectStarsNonPi (A.Ind _ a1 n1 _) (Ind a2 n2 _) | n1 /= n2 = __IMPOSSIBLE__
collectStarsNonPi (A.Ind _ a1 n1 _) (Ind (Size a2) n2 _) | n1 == n2 = return res
  where
    res | a1 /= Star || base a2 == Nothing = []
        | a1 == Star                       = [fromJust (base a2)]
collectStarsNonPi e                 (App (Ind (Size a2) n2 _) args2) = do
  rs <- zipWithM collectStars args1 args2
  return $ res ++ concat rs
  where
    (A.Ind _ a1 n1 _, args1) = A.unApp e
    res | a1 /= Star || base a2 == Nothing = []
        | a1 == Star                       = [fromJust (base a2)]
collectStarsNonPi a b =
  do
    traceTCM 20 $ hsep [text "collectStarsNonPi", prettyTCM a,
                        text "and", prettyTCM b]
    return []

collectStarsBind :: (MonadTCM tcm) => A.Context -> Context -> tcm [StageVar]
collectStarsBind CtxEmpty CtxEmpty = return []
collectStarsBind (A.Bind r [] e :> bs) ctx = collectStarsBind bs ctx
collectStarsBind (A.Bind r (x:xs) e :>  bs) (t :> ctx)  = do
  rs1 <- collectStars (fromJust (implicitValue e)) (bindType t)
  rs2 <- collectStarsBind (A.Bind r xs e :> bs) ctx
  return $ rs1 ++ rs2
collectStarsBind _ _ = __IMPOSSIBLE__


extractIndType :: (MonadTCM tcm) => Type -> tcm (Name, InductiveKind, StageVar)
extractIndType tp =
  do
    tp' <- whnF tp
    let (a, n) = case tp' of
                   App (Ind a n _) _ -> (a, n)
                   Ind a n _         -> (a, n)
    i <- getGlobal n -- must be (co-)inductive
    return (n, indKind i, extractSvar a)

  where
    extractSvar :: Annot -> StageVar
    extractSvar (Size (Svar i)) = i
    extractSvar _               = __IMPOSSIBLE__ -- sanity check


inferFix :: (MonadTCM tcm) => A.FixExpr -> tcm (Term, Type)
inferFix (A.FixExpr r CoI num f tp body) =
  do
    allOld <- allStages

    traceTCM 20 $ hsep [text "Typechecking cofixpoint type: ",
                        prettyTCM tp]
    (tp', s') <- inferType tp
    traceTCM 20 $ hsep [text "Typechecked cofixpoint type: ", prettyTCM tp']

    is <- collectStars tp tp'
    traceTCM 30 $ hsep [text "Star stages:", prettyTCM is]

    -- Check that the fix type is correct
    (ctx, tpRes) <- unfoldPi tp'
    (iName, iKind, alpha) <- extractIndType tpRes
    when (iKind /= CoI) $ error "return type is inductive"

    let shiftStar s@(Size (Svar x)) | x `elem` is = Size (Hat (Svar x))
                                    | otherwise = s
        shiftStar s = s

        sctx = modifySize shiftStar ctx
        stpRes = modifySize shiftStar tpRes

        tpCofix = mkPi sctx stpRes

    body' <- pushBind (mkBind f tp') $ check body (I.lift 1 0 tpCofix)

    -- checknig constraints
    -- Calling recCheck
    let vNeq = (allOld ++ fAnnot tp' ++ fAnnot body') \\ (is ++ [inftyStageVar])
    alls <- allStages
    cOld <- allConstraints
    traceTCM 15 $ (hsep [text "\nCOI calling recCheck alpha = ", prettyTCM alpha]
                   $$ nest 2 (vcat [text "vStar =" <+> prettyTCM is,
                                    text "all other =" <+> prettyTCM (alls \\ is),
                                    text "vNeq =" <+> prettyTCM vNeq,
                                    text "C = \n" <+> text (show cOld)]))
    -- add Constraints to ensure that alpha appears positively in the return type
    traceTCM 15 $ (hsep [text "shifting ", prettyTCM sctx
                        , text " <~ ", prettyTCM ctx])
    _ <- subType sctx ctx

    let recRes = recCheck alpha is vNeq cOld

    case recRes of
      Left cNew -> do newConstraints cNew
      Right xs  -> do error ("COFIX " ++ show xs)

    traceTCM 15 $ hsep [text "result recCheck ", text $ show recRes]

    return (Fix (FixTerm CoI num f ctxEmpty (eraseSize tp') body'), tp')


inferFix fixexpr@(A.FixExpr r I num f tp body) =
    do allOld <- allStages -- all stages before typechecking fix
       traceTCM 20 $ hsep [text "Typechecking fixpoint type: ",
                           prettyTCM tp]
       (tp', s) <- inferType tp
       traceTCM 15 $ hsep [text "Typechecked fixpoint type: ", prettyTCM tp']
       is <- collectStars tp tp'
       traceTCM 30 $ hsep [text "Star stages:", prettyTCM is]

       -- e <- ask
       -- traceTCM_ ["V* ", show is, " in ", show tp', "\nenv :", show e]

       -- Check that the fix type is correct
       (ctx, tpRes) <- unfoldPi tp'
       when (size ctx < num) $ error $ "error " ++ show r ++ ": fix should have at least " ++ show num ++ " argument" ++ if num > 0 then "s" else ""
       -- traceTCM_ ["unfold type fix\n", show ctx, "   ->   ", show tpRes]

       let (args, ctx') = ctxSplitAt (num - 1) ctx
           (recArg, rest) = ctxSplit ctx'
       -- TODO: check what to do with star appearing in args before recArg
       --       for the moment, assume that no star appear before recArg
           shiftStar s@(Size (Svar x)) | x `elem` is = Size (Hat (Svar x))
                                       | otherwise = s
           shiftStar s = s
           srecArg = modifySize shiftStar recArg
           srest = modifySize shiftStar rest
           stpRes = modifySize shiftStar tpRes

           tpFix = mkPi (args <> (srecArg :> srest)) stpRes

       -- meta stage var that must be assigned to a real stage var
       (iName, iKind, alpha) <- extractIndType (bindType recArg)
       when (iKind /= I) $ error "recursive type is coinductive"

       body' <- pushBind (mkBind f tp') $ check body (I.lift 1 0 tpFix)

       -- Calling recCheck
       let vNeq = (allOld ++ fAnnot tp' ++ fAnnot body') \\ (is ++ [inftyStageVar])
       alls <- allStages
       cOld <- allConstraints
       traceTCM 15 $ (hsep [text "I calling recCheck alpha = ", prettyTCM alpha]
                      $$ nest 2 (vcat [text "vStar =" <+> prettyTCM is,
                                       text "all other =" <+> prettyTCM (alls \\ is),
                                       text "vNeq =" <+> prettyTCM vNeq,
                                       text "C =" <+> text (show cOld)]))

       -- add Constraints to ensure that alpha appears positively in the return type
       traceTCM 15 $ (hsep [text "shifting ", pushBind srecArg $ prettyTCM srest
                           , text " <~ ", pushBind srecArg $ prettyTCM rest])
       traceTCM 15 $ (hsep [text "shifting ", pushCtx (srecArg :> srest) $ prettyTCM tpRes
                           , text " <~ ", pushCtx (srecArg :> srest) $ prettyTCM stpRes])
       _ <- pushBind srecArg $ subType srest rest -- was rest <~ srest
       _ <- pushCtx (srecArg :> srest) $ subType tpRes stpRes


       let recRes = recCheck alpha is vNeq cOld

       case recRes of
         Left cNew -> do newConstraints cNew
         Right xs  -> do -- traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                         traceTCM 15 $ vcat [ text "FIX FAILED ON CTX"
                                            , (ask >>= prettyTCM)
                                            , text "------------------------"
                                            , prettyTCM (A.Fix fixexpr) ]
                         error ("FIX " ++ show xs)


       traceTCM 15 $ hsep [text "result recCheck ", text $ show recRes]
       -- Final result
       return (Fix (FixTerm I num f (eraseSize ctxEmpty) (eraseSize tp') body'), tp')

checkFixType :: (MonadTCM tcm) => Bind -> tcm StageVar
checkFixType (Bind _ _ tp Nothing) =
  do
    tp' <- whnF tp
    case tp' of
      App (Ind a _ _) _ ->
        case a of
          Size (Svar i) -> return i
          _ -> __IMPOSSIBLE__ -- sanity check
      Ind a _ _        ->
        case a of
          Size (Svar i) -> return i
          _ -> __IMPOSSIBLE__ -- sanity check
      _ -> error "recursive argument is not of inductive type"
checkFixType _ = error "recursive argument is a definition"
