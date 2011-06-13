{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses
  #-}

module Kernel.Inductive where

import Control.Monad.Reader

import qualified Data.Foldable as Fold

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Syntax.Size
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import {-# SOURCE #-} Kernel.TypeChecking
import Utils.Misc

{---
TODO:
 - positivity check in constructors
---}

-- | Type-checks an inductive definition returning a list of global definitions
--   for the inductive type and the constructors
inferInd :: (MonadTCM tcm) => A.InductiveDef -> tcm [(Name, Global)]
inferInd ind@(A.InductiveDef name pars tp constrs) =
    do -- traceTCM $ "Checking inductive definition\n" ++ show ind
       ((pars',pols'), _) <- inferParamList pars
       -- traceTCM $ "Parameters\n" ++ show pars'
       let bindPars' =  pars'
       (tp', s2)  <- pushCtx pars' $ infer tp
       -- traceTCM $ "Type\n" ++ show tp'
       _          <- isSort s2
       (args, s3) <- isArity (getRange tp) tp'
       cs         <- mapM (pushCtx pars' . flip checkConstr (name, bindPars', args, s3)) constrs
       -- traceTCM $ "Constructors\n" ++ show cs
       return $ (name, Inductive pars' pols' args s3 constrNames) : fillIds cs
         where fillIds cs = map (\(idConstr, (x, c)) -> (x, c { constrId = idConstr })) (zip [0..] cs)
               constrNames = map A.constrName constrs

-- | Checks that a type is an arity.
--   Code is ugly
isArity :: (MonadTCM tcm) => Range -> Type -> tcm (Context, Sort)
isArity _ t =
  do (bs1, t1) <- unfoldPi t
     case t1 of
       Sort s -> return (bs1, s)
       _      -> error "Not arity. replace by error in TCErr"


inferParam :: (MonadTCM tcm) => A.Parameter -> tcm ((Context, [Polarity]), Sort)
inferParam (A.Parameter _ names tp) =
    do (tp', s) <- infer tp
       s' <- isSort s
       return (mkBindsSameType names tp', s')
      where
        mkBindsSameType_ :: [(Name, Polarity)] -> Type -> Int -> (Context,[Polarity])
        mkBindsSameType_ [] _ _ = (empCtx,[])
        mkBindsSameType_ ((x,pol):xs) t k = ((Bind x (I.lift k 0 t)) <| ctx,
                                             pol : pols)
          where (ctx, pols) = mkBindsSameType_ xs t (k + 1)

        mkBindsSameType xs t = mkBindsSameType_ xs t 0

inferParamList :: (MonadTCM tcm) => [A.Parameter] -> tcm ((Context, [Polarity]), Sort)
inferParamList [] = return ((empCtx, []), Prop)
inferParamList (p:ps) = do ((ctx1, pol1), s1) <- inferParam p
                           ((ctx2, pol2), s2) <- pushCtx ctx1 $ inferParamList ps
                           return ((ctx1 +: ctx2, pol1 ++ pol2), max s1 s2)


checkConstr :: (MonadTCM tcm) =>  A.Constructor -> (Name, Context, Context, Sort) -> tcm (Name, Global)
checkConstr (A.Constructor _ name tp _)
            (nmInd, parsInd, indicesInd, sortInd) =
    do (tp', s) <- local (indBind:) $  infer tp
       s' <- isSort s
       unlessM (conversion sortInd s') $ error "Error in constructor. Make up value for TCErr"
       -- traceTCM $ "Constructor checking: " ++ show tp ++ " --> " ++ show tp'
       (args, indices) <- isConstrType nmInd numPars (subst (Ind Empty nmInd) tp')
       return (name, Constructor nmInd 0 parsInd args indices)
                     -- id is filled elsewhere
      where numPars = ctxLen parsInd
            indType
              | ctxLen parsInd + ctxLen indicesInd == 0 = Sort sortInd
              | otherwise = Pi (parsInd +: indicesInd) (Sort sortInd)
            indBind = Bind nmInd indType

-- TODO: check that inductive type are applied to the parameters in order
--       check polarities of arguments and strict positivity of the inductive
--       type
isConstrType :: (MonadTCM tcm) => Name -> Int -> Type -> tcm (Context, [Term])
isConstrType nmInd numPars tp =
  do (bs1, tp') <- unfoldPi tp
     tp1 <- whnf tp'
     case tp1 of
       App (Ind _ i) args -> do when (i /= nmInd) $ error "Not constructor 1"
                                return (bs1, drop numPars args)
       Ind _ i            -> do when (i /= nmInd) $ error "Not constructor 1'"
                                return (bs1, [])
       t'                 -> error $ "Not constructor 2. Make up value in TCErr " ++ show t'
