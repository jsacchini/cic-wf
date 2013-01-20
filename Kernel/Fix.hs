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

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, CPP
  #-}

module Kernel.Fix where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader

import Data.List
import Data.Maybe

import Syntax.Common
import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Syntax.InternaltoAbstract
import Syntax.Size

import Kernel.Conversion
import Kernel.Constraints
import Kernel.RecCheck
import Kernel.PrettyTCM
import Kernel.TCM
import {-# SOURCE #-} Kernel.TypeChecking
import Kernel.Whnf

import Utils.Pretty
import Utils.Sized


-- | 'collectStars' @e@ @t@ assumes that @e@ and @t@ have the same shape
--   Returns the list of stage variables occuring in @t@ whose corresponding
--   position in @e@ has a star.
--   @t@ is the typed version of @e@ so they should have the same shape.
--   For now, we assume that @e@ and @t@ are simple types, so star occur in
--   (co-)inductive types directly under products.
collectStars :: (MonadTCM tcm) => A.Expr -> Type -> tcm [StageVar]
collectStars (A.Pi _ bs e)     (Pi ctx t)    = do
  rs2 <- collectStars e t
  rs1 <- collectStarsBind bs ctx
  return $ rs1 ++ rs2
collectStars e                 (Pi EmptyCtx t2) = collectStars e t2
collectStars (A.Arrow _ e1 e2) (Pi (ExtendCtx t1 ctx) t2) = do
  traceTCM 85 $ text "here"
  rs2 <- collectStars e2 (Pi ctx t2)
  rs1 <- collectStars e1 (bindType t1)
  return $  rs1 ++ rs2
collectStars (A.Ind _ a1 n1) (Ind a2 n2) | n1 /= n2 = __IMPOSSIBLE__
collectStars (A.Ind _ a1 n1) (Ind (Size a2) n2) | n1 == n2 = return res
  where
    res | a1 /= Star || base a2 == Nothing = []
        | a1 == Star                       = [fromJust (base a2)]
collectStars e               (App (Ind (Size a2) n2) args2) = do
  rs <- zipWithM collectStars args1 args2
  return $ res ++ concat rs
  where
    (A.Ind _ a1 n1, args1) = A.destroyApp e
    res | a1 /= Star || base a2 == Nothing = []
        | a1 == Star                       = [fromJust (base a2)]
collectStars _ _ = return []

collectStarsBind :: (MonadTCM tcm) => [A.Bind] -> Context -> tcm [StageVar]
collectStarsBind []                     EmptyCtx          = return []
collectStarsBind (A.Bind r _ [] e:bs)     (ExtendCtx _ ctx) = collectStarsBind bs ctx
collectStarsBind (A.Bind r _ (x:xs) e:bs) (ExtendCtx t ctx) = do
  rs1 <- collectStars e (bindType t)
  rs2 <- collectStarsBind (A.Bind r False xs e:bs) (ExtendCtx t ctx)
  return $ rs1 ++ rs2
collectStarsBind _ _ = __IMPOSSIBLE__


extractIndType :: (MonadTCM tcm) => Type -> tcm (Name, InductiveKind, StageVar)
extractIndType tp =
  do
    tp' <- whnf tp
    let (a, n) = case tp' of
                   App (Ind a n) _ -> (a, n)
                   Ind a n         -> (a, n)
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
                        prettyPrintTCM tp]
    (tp', s) <- infer tp
    traceTCM 20 $ hsep [text "Result: ", prettyPrintTCM tp']
    s' <- isSort s

    is <- collectStars tp tp'
    traceTCM 30 $ hsep [text "Star stages:", prettyPrintTCM is]

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
    let vNeq = (allOld ++ listAnnot tp' ++ listAnnot body') \\ (is ++ [0])
    alls <- allStages
    cOld <- allConstraints
    traceTCM 30 $ (hsep [text "calling recCheck alpha = ", prettyPrintTCM alpha]
                   $$ nest 2 (vcat [text "vStar = " <> prettyPrintTCM is,
                                    text "all other = " <> prettyPrintTCM (alls \\ is),
                                    text "vNeq = " <> prettyPrintTCM vNeq,
                                    text "C = " <> text (show cOld)]))
    -- add Constraints to ensure that alpha appears positively in the return type
    traceTCM 30 $ (hsep [text "shifting ", prettyPrintTCM sctx, text " <~ ",
                        prettyPrintTCM ctx])
    _ <- sctx <~ ctx

    let recRes = recCheck alpha is vNeq cOld

    case recRes of
      Left cNew -> do newConstraints cNew
      Right xs  -> do error "COFIX"

    return (Fix CoI num f empCtx (eraseSize tp') body', tp')


inferFix (A.FixExpr r I num f tp body) =
    do allOld <- allStages -- all stages before typechecking fix
       traceTCM 20 $ hsep [text "Typechecking fixpoint type: ",
                           prettyPrintTCM tp]
       (tp', s) <- infer tp
       traceTCM 20 $ hsep [text "Result: ", prettyPrintTCM tp']
       is <- collectStars tp tp'
       traceTCM 30 $ hsep [text "Star stages:", prettyPrintTCM is]

       -- e <- ask
       -- traceTCM_ ["V* ", show is, " in ", show tp', "\nenv :", show e]
       _ <- isSort s

       -- Check that the fix type is correct
       (ctx, tpRes) <- unfoldPi tp'
       when (size ctx < num) $ error $ "error " ++ show r ++ ": fix should have at least " ++ show num ++ " argument" ++ if num > 0 then "s" else ""
       -- traceTCM_ ["unfold type fix\n", show ctx, "   ->   ", show tpRes]

       let (args, ExtendCtx recArg rest) = ctxSplitAt (num - 1) ctx
       -- TODO: check what to do with star appearing in args before recArg
       --       for the moment, assume that no star appear before recArg
           shiftStar s@(Size (Svar x)) | x `elem` is = Size (Hat (Svar x))
                                       | otherwise = s
           shiftStar s = s
           srecArg = modifySize shiftStar recArg
           srest = modifySize shiftStar rest
           stpRes = modifySize shiftStar tpRes

           tpFix = mkPi (args +: (srecArg <| srest)) stpRes

       -- meta stage var that must be assigned to a real stage var
       (iName, iKind, alpha) <- extractIndType (bindType recArg)
       when (iKind /= I) $ error "recursive type is coinductive"
       -- traceTCM_ ["alpha = ", show alpha]

       -- traceTCM_ ["recursive type ", show tp', "\n body type ", show tpFix]

       -- Checking the body
       -- traceTCM_ ["checking body ", show tp', "\nbody ", show body, "\n fix type = ", show tpFix]
       body' <- pushBind (mkBind f tp') $ check body (I.lift 1 0 tpFix)
       -- traceTCM_ ["body checked"]

       -- rbody' <- pushBind (Bind f tp') $ reify body'
       -- rtp' <- reify tp'
       -- traceTCM_ ["FIX\n", show (prettyPrint rbody'), "\n : ", show (prettyPrint rtp')]

       -- Calling recCheck
       let vNeq = (allOld ++ listAnnot tp' ++ listAnnot body') \\ (is ++ [inftyStageVar])
       alls <- allStages
       cOld <- allConstraints
       -- traceTCM_ ["calling recCheck\nalpha = ", show alpha, "\nvStar = ", show is, "\nall other = ", show (alls \\ is), "\nvNeq = ", show vNeq, "\nC = ", show cOld]

       -- add Constraints to ensure that alpha appears positively in the return
       -- type
       -- traceTCM_ ["shifting ", show rest, " <~ ", show srest, "\n", show tpRes, " <~ ", show stpRes]
       _ <- pushBind srecArg $ srest <~ rest -- was rest <~ srest
       _ <- pushCtx (srecArg <| srest) $ tpRes <~ stpRes

       -- traceTCM_ ["added constraints"]

       let recRes = recCheck alpha is vNeq cOld

       case recRes of
         Left cNew -> do newConstraints cNew
                         -- traceTCM_ ["fix passed!"]
         Right xs  -> do -- traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                         error "FIX"


       -- traceTCM_ ["checked fix\n", show (Fix num f empCtx tp' body'), "\n", show r, "\nof type ", show tp']

       -- Final result
       return (Fix I num f (eraseSize empCtx) (eraseSize tp') body', tp')

checkFixType :: (MonadTCM tcm) => Bind -> tcm StageVar
checkFixType (Bind _ _ tp Nothing) =
  do
    tp' <- whnf tp
    case tp' of
      App (Ind a _) _ -> case a of
                           Size (Svar i) -> return i
                           _ -> __IMPOSSIBLE__ -- sanity check
      Ind a _         -> case a of
                           Size (Svar i) -> return i
                           _ -> __IMPOSSIBLE__ -- sanity check
      _ -> error "recursive argument is not of inductive type"
checkFixType _ = error "recursive argument is a definition"

