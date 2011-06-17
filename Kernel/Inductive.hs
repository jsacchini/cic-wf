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
import Utils.Sized

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
isArity :: (MonadTCM tcm) => Range -> Type -> tcm (Context, Sort)
isArity _ t =
  do (ctx, t1) <- unfoldPi t
     case t1 of
       Sort s -> return (ctx, s)
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
       let indBind = Bind nmInd (mkPi (parsInd +: indicesInd) (Sort sortInd))
       (args, indices, recArgs) <- pushBind indBind $
                                   isConstrType name nmInd numPars tp'

       -- We replace all occurrences of other inductive types with infty
       -- The inductive type being typechecked here is assigned Star
       -- When checking a constructor, we can replace Star with a fresh
       -- variable
       let argsInfty = modifySize (const (Size Infty)) args
           indicesInfty = modifySize (const (Size Infty)) indices
       return (name, Constructor nmInd 0 parsInd (subst (Ind Star nmInd) argsInfty) recArgs indicesInfty)
                     -- id is filled elsewhere
      where numPars = ctxLen parsInd
            indType
              | ctxLen parsInd + ctxLen indicesInd == 0 = Sort sortInd
              | otherwise = Pi (parsInd +: indicesInd) (Sort sortInd)
            indBind = Bind nmInd indType

-- TODO: check that inductive type are applied to the parameters in order
--       check polarities of arguments and strict positivity of the inductive
--       type
isConstrType :: (MonadTCM tcm) =>
                Name -> Name -> Int -> Type -> tcm (Context, [Term], [Int])
isConstrType nmConstr nmInd numPars tp =
  do (ctx, tpRet) <- unfoldPi tp
     -- traceTCM_ ["checking positivity ", show nmConstr, ": ", show ctx, ", ", show tpRet]
     recArgs <- checkStrictPos nmConstr ctx
     -- traceTCM_ ["recArgs ", show recArgs]
     let numInd = size ctx -- bound index of the inductive type in the
                           -- return type
     case tpRet of
       App (Bound i) args -> do
         when (isFree numInd args) $ error "inductive var appears in the arguments in the return type"
         when (i /= numInd) $ error $ "Not constructor " ++ show nmConstr
         return (ctx, drop numPars args, recArgs)

       Bound i -> do
         when (i /= numInd) $ error $ "Not constructor other " ++ show nmConstr
         return (ctx, [], recArgs)

       t'                 -> error $ "Not constructor 2. Make up value in TCErr " ++ show t' ++ " on " ++ show nmConstr


-- | Checks that the inductive type var (Bound var 0) appears strictly positive
--   in the arguments of a constructor. Returns the list of recursive arguments.
checkStrictPos :: (MonadTCM tcm) => Name -> Context -> tcm [Int]
checkStrictPos nmConstr = cSP 0
  where
    cSP _ EmptyCtx = return []
    cSP k (ExtendCtx b@(Bind x t) ctx)
      | not (isFree k t) = pushBind b $ cSP (k + 1) ctx
      | otherwise = do
        -- traceTCM_ ["considering arg ", show k, "  -->  ", show (Bind x t)]
        (ctx1, t1) <- unfoldPi t
        when (isFree k ctx1) $ error $ "inductive type not strictly positive: " ++ show nmConstr
        case t1 of
          App (Bound i) args -> do
            when (isFree (k + size ctx1) args) $ error $ "inductive type appears as argument: " ++ show nmConstr
            when (i /= k + size ctx1) $ error $ "I don't think this is possible: expected " ++ show (k + size ctx1) ++ " but found " ++ show i
            recArgs <- pushBind b $ cSP (k + 1) ctx
            return $ k : recArgs
          Bound i -> do
            when (i /= k + size ctx1) $ error $ "I don't think this is possible either: expected " ++ show (k + size ctx1) ++ " but found " ++ show i
            recArgs <- pushBind b $ cSP (k + 1) ctx
            return $ k : recArgs
          _ -> error $ "not valid type " ++ show nmConstr
