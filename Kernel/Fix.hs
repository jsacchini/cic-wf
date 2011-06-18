{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, CPP
  #-}

module Kernel.Fix where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader

import Data.List

import Syntax.Common
import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Syntax.InternaltoAbstract
import Syntax.Size

import Kernel.Conversion
import Kernel.Constraints
import Kernel.TCM
import {-# SOURCE #-} Kernel.TypeChecking
import Kernel.Whnf

import Utils.Pretty
import Utils.Sized

inferFix :: (MonadTCM tcm) => A.FixExpr -> tcm (Term, Type)
inferFix (A.FixExpr r num f tp body) =
    do resetStarStages
       allOld <- allStages -- all stages before typechecking fix
       (tp', s) <- infer tp
       is <- getStarStages
       
       -- e <- ask
       -- traceTCM_ ["V* ", show is, " in ", show tp', "\nenv :", show e]
       resetStarStages
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
       alpha <- checkFixType recArg
       -- traceTCM_ ["alpha = ", show alpha]

       -- traceTCM_ ["recursive type ", show tp', "\n body type ", show tpFix]

       -- Checking the body
       -- traceTCM_ ["checking body ", show tp', "\nbody ", show body, "\n fix type = ", show tpFix]
       body' <- pushBind (Bind f tp') $ check body (I.lift 1 0 tpFix)
       -- traceTCM_ ["body checked"]

       rbody' <- pushBind (Bind f tp') $ reify body'
       rtp' <- reify tp'
       -- traceTCM_ ["FIX\n", show (prettyPrint rbody'), "\n : ", show (prettyPrint rtp')]

       -- Calling recCheck
       let vNeq = (allOld ++ listAnnot tp' ++ listAnnot body') \\ (is ++ [0])
       alls <- allStages
       cOld <- allConstraints
       -- traceTCM_ ["calling recCheck\nalpha = ", show alpha, "\nvStar = ", show is, "\nall other = ", show (alls \\ is), "\nvNeq = ", show vNeq, "\nC = ", show cOld]

       -- add Constraints to ensure that alpha appears positively in the return
       -- type
       -- traceTCM_ ["shifting ", show rest, " <~ ", show srest, "\n", show tpRes, " <~ ", show stpRes]
       _ <- pushBind srecArg $ rest <~ srest
       _ <- pushCtx (srecArg <| srest) $ tpRes <~ stpRes

       -- traceTCM_ ["added constraints"]

       let recRes = recCheck alpha is vNeq cOld

       case recRes of
         Left cNew -> do newConstraints cNew
                         -- traceTCM_ ["fix passed!"]
         Right xs  -> do traceTCM_ ["recursion BROKEN in\n", show body', "\n : ", show tp', "\n stage vars: ", show xs]
                         error "FIX"


       -- traceTCM_ ["checked fix\n", show (Fix num f empCtx tp' body'), "\n", show r, "\nof type ", show tp']

       -- Final result
       return (Fix num f (eraseSize empCtx) (eraseSize tp') body', tp')

      where checkFixType :: (MonadTCM tcm) => Bind -> tcm Int
            checkFixType (Bind _ tp) = do
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