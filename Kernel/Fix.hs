{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses
  #-}

module Kernel.Fix where

import Control.Monad.Reader

import Syntax.Common
import Syntax.Internal hiding (lift)
import qualified Syntax.Abstract as A
import Syntax.InternaltoAbstract
import Syntax.Size

import Kernel.Conversion
import Kernel.TCM
import {-# SOURCE #-} Kernel.TypeChecking
import Kernel.Whnf

import Utils.Pretty
import Utils.Sized

inferFix :: (MonadTCM tcm) => A.FixExpr -> tcm (Term, Type)
inferFix (A.FixExpr r num f tp body) =
    do resetStarStages
       (tp', s) <- infer tp
       is <- getStarStages
       -- traceTCM_ ["star vars ", show is, " in ", show tp']
       resetStarStages
       _ <- isSort s

       -- Check that the fix type is correct
       (ctx, tpRes) <- unfoldPi tp'
       when (size ctx < num) $ error $ "error " ++ show r ++ ": fix should have at least " ++ show num ++ " argument" ++ if num > 0 then "s" else ""
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

       -- traceTCM_ ["checking against type ", show tpFix]
       (body', u) <- pushBind (Bind f tp') $ infer body
       bb <- pushBind (Bind f tp') $ reify body'
       -- traceTCM_ ["checked body ", show (prettyPrint bb), " \n: ", show u, "\n expected: ", show tp']
       b <- conversion tp' u
       -- traceTCM_ ["type converted "]
       tpr <- reify tp'
       ur <- reify u
       unless b $ error $ "fix error " ++ show (prettyPrint tpr) ++ " == " ++ show (prettyPrint ur)
       return (Fix num f (eraseSize empCtx) (eraseSize tp') body', tp')
