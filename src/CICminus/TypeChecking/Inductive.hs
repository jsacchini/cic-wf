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

module CICminus.TypeChecking.Inductive where

import           Control.Monad.Reader

import           Data.Monoid

import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal           hiding (lift)
import           CICminus.Syntax.Internal           as I
import           CICminus.Syntax.Position
-- import CICminus.Syntax.Size
import qualified CICminus.Syntax.Abstract           as A
import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.PrettyTCM    hiding ((<>))
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.TypeChecking
import           CICminus.TypeChecking.Whnf

import           CICminus.Utils.Impossible
import           CICminus.Utils.Misc
import           CICminus.Utils.Sized

-- TODO: check that inductive types are applied to parameters in order

-- | Type-checks an inductive definition returning a list of global definitions
--   for the inductive type and the constructors
inferInd :: (MonadTCM tcm) => A.InductiveDef -> tcm [Named Global]
inferInd i@(A.InductiveDef {}) =
    do -- traceTCM $ "Checking inductive definition\n" ++ show ind
       (pars', _) <- inferBinds (A.indPars i)
       (tp', s2)  <- pushCtx pars' $ inferType (A.indType i)
       -- traceTCM $ "Type\n" ++ show tp'
       (args, s3) <- isArity (range (A.indType i)) tp'
       cs         <- mapM (pushCtx pars' . flip checkConstr (A.indName i, pars', args, s3)) (A.indConstr i)
       -- traceTCM 30 $ text ("Constructors\n" ++ show cs)

       -- Preparing the constructors
       -- We replace all occurrences of other inductive types with infty
       -- The inductive type being typechecked here is assigned Star
       -- When checking a constructor, we can replace Star with a fresh
       -- variable
       let replInfty :: (HasAnnot a) => a -> a
           replInfty = modifySize (const (Stage I.Infty))
           annots = listAnnot tp' ++ listAnnot (map namedValue cs)
           annotToNode (Stage (StageVar s _)) = VarNode s
           annotToNode (Stage Infty) = InftyNode
           annotToNode _ = __IMPOSSIBLE__
           numPars = size pars'
           replInd c = c { constrArgs = substIndCtx (A.indName i) numPars 0 (constrArgs c) }
           cs' = map (fmap (replInd . replInfty)) cs

       pushCtx pars' $ traceTCM 30 $ text "Constructors!!!"
         <+> prettyTCM (map (constrArgs . namedValue) cs)
       pushCtx pars' $ traceTCM 30 $ text "Constructors!!!"
         <+> prettyTCM (map (constrArgs . namedValue) cs')

       removeStages (map annotToNode annots)
       return $ mkNamed (A.indName i) (Inductive (A.indKind i) (replInfty pars') (A.indPolarities i) (replInfty args) s3 constrNames) : fillIds cs'
         where fillIds cs = map (\(idConstr, c) -> fmap (\c' -> c' { constrId = idConstr }) c) (zip [0..] cs)
               constrNames = map A.constrName (A.indConstr i)

-- | Checks that a type is an arity.
isArity :: (MonadTCM tcm) => Range -> Type -> tcm (Context, Sort)
isArity _ t =
  do (ctx, t1) <- unfoldPi t
     case t1 of
       Sort s -> return (ctx, s)
       _      -> error "Not arity. replace by error in TCErr"


-- | substInd replaces the occurence of a bound variable for an inductive type
-- TODO: check that the inductive type is applied to the parameters in order
substInd :: Name -> Int -> Int -> Term -> Term
substInd nmInd numPars var tp =
  case unApp tp of
    (Pi ctx tp', []) ->
      mkPi (substIndCtx nmInd numPars var ctx)
      (substInd nmInd numPars (var + size ctx) tp')
    -- (Bound k, []) ->
    --   if k == var
    --   then if numPars == 0 then Ind Star nmInd []
    --        else __IMPOSSIBLE__
    --   else if k > var
    --        then Bound (k - 1)
    --        else Bound k
    (Ind a x pars, []) -> Ind a x (map (substInd nmInd numPars var) pars)
    (func, args) ->
      case func of
        Bound k -> if k == var
                   then mkApp (Ind Star nmInd pars) inds
                   else if k > var
                        then mkApp (Bound (k-1)) args'
                        else mkApp (Bound k) args'
        _ -> mkApp func' args'
             -- We know var occurs strictly positive, so
             -- it cannot occur in func nor args
      where
        func' = I.lift (-1) var func -- substInd nmInd numPars var func
        args' = I.lift (-1) var args --map (substInd nmInd numPars var) args
        (pars, inds) = splitAt numPars args'


substIndCtx :: Name -> Int -> Int -> Context -> Context
substIndCtx nmInd numPars var ctx =
  case ctx of
    CtxEmpty -> CtxEmpty
    b :> ctx' ->
      b' :> substIndCtx nmInd numPars (var + 1) ctx'
        where
          tp = fmap (substInd nmInd numPars var) (bindType b)
          b' = b { bindType = tp }


checkConstr :: (MonadTCM tcm) =>  A.Constructor -> (Name, Context, Context, Sort) -> tcm (Named Global)
checkConstr (A.Constructor _ name tp)
            (nmInd, parsInd, indicesInd, sortInd) =
    do
       traceTCM 30 $ hsep [ text "CHECKCONSTR"
                          , text "from:" <+> (pushBind indBind $ prettyTCM tp) ]
       (tp', s') <- pushBind indBind $  inferType tp
       traceTCM 30 $ hsep [ text "CHECKCONSTR"
                          , text "to:" <+> (pushBind indBind $ prettyTCM tp')
                          , text "of type:" <+> (pushBind indBind $ prettyTCM s') ]
       traceTCM 30 $ vcat [ text "Sort of inductive type:" <+> prettyTCM sortInd
                          , text "Sort of constructor:" <+> prettyTCM s' ]
       unlessM (subType s' sortInd) $ error $ "sort of constructor " ++ show name ++ " is "++ show s' ++ " but inductive type " ++ show nmInd ++ " has sort " ++ show sortInd
       let indBind = mkBind nmInd (mkPi (parsInd <> indicesInd) (Sort sortInd))
       (args, indices, recArgs) <- pushBind indBind $
                                   isConstrType name nmInd numPars tp'

       return $ mkNamed name (Constructor nmInd 0 parsInd args recArgs indices)
                     -- id is filled elsewhere
      where numPars = ctxLen parsInd
            indType
              | size parsInd + size indicesInd == 0 = Sort sortInd
              | otherwise = Pi (parsInd <> indicesInd) (Sort sortInd)
            indBind = mkBind nmInd indType

-- TODO: check that inductive type are applied to the parameters in order
--       check polarities of arguments and strict positivity of the inductive
--       type
isConstrType :: (MonadTCM tcm) =>
                Name -> Name -> Int -> Type -> tcm (Context, [Term], [Int])
isConstrType nmConstr nmInd numPars tp =
  do (ctx, tpRet) <- unfoldPi tp
     traceTCM 30 $ hsep [ text "checking positivity "
                        , prettyTCM nmConstr
                        , text ": "
                        , prettyTCM tp ]
     recArgs <- checkStrictPos nmConstr ctx
     -- traceTCM_ ["recArgs ", show recArgs]
     let numInd = size ctx -- bound index of the inductive type in the
                           -- return type
     case tpRet of
       App (Bound i) args -> do
         when (isFree numInd args) $ error "inductive var appears in the arguments in the return type"
         when (i /= numInd) $ error $ "Not constructor " ++ show nmConstr
         traceTCM 30 $ (text "isCONSTRTYPE" $$
                        nest 3 (vcat [ text "TYPE:" <+> prettyTCM ctx
                                     , text "ARGS: " <+> hsep (map (pushCtx ctx . prettyTCM) (drop numPars args))
                                     , text "REC ARGS: "<+> hsep (map prettyTCM recArgs)
                                     ]))
         -- numInd does not occur in args, but we replace it to remove it from
         -- the context; this way the indices depend only on the parameters and
         -- constructor arguments
         let args' = substN numInd (Ind Star nmInd []) args
         return (ctx, drop numPars args', recArgs)

       Bound i -> do
         when (i /= numInd) $ error $ "Not constructor other " ++ show nmConstr
         return (ctx, [], recArgs)

       t'                 -> error $ "Not constructor 2. Make up value in TCErr " -- ++ show t' ++ " on " ++ show nmConstr


-- | Checks that the inductive type var (Bound var 0) appears strictly positive
--   in the arguments of a constructor. Returns the list of recursive arguments.
checkStrictPos :: (MonadTCM tcm) => Name -> Context -> tcm [Int]
checkStrictPos nmConstr ctx = cSP 0 ctx
  where
    cSP _ CtxEmpty = return []
    cSP k ((b@(Bind x t Nothing)) :> ctx)
      | not (isFree k t) = pushBind b $ cSP (k + 1) ctx
      | otherwise = do
        -- traceTCM_ ["considering arg ", show k, "  -->  ", show (Bind x t)]
        (ctx1, t1) <- unfoldPi (unArg t)
        when (isFree k ctx1) $ error $ "inductive type not strictly positive: " ++ show nmConstr
        case unApp t1 of
          (Bound i,  args) -> do
            when (isFree (k + size ctx1) args) $ error $ "inductive type appears as argument: " ++ show nmConstr
            when (i /= k + size ctx1) $ error $ "I don't think this is possible: expected " ++ show (k + size ctx1) ++ " but found " ++ show i
            recArgs <- pushBind b $ cSP (k + 1) ctx
            return $ k : recArgs
          (Ind an nmInd parsInd, argsInd) -> do
            ind <- getGlobal nmInd
            let pols = indPol ind
            mapM_ (checkSPTypePol nmConstr (k+size ctx1)) (zip pols parsInd)
            recArgs <- pushBind b $ cSP (k + 1) ctx
            return $ k : recArgs
          _ -> error $ "not valid type " ++ show nmConstr
    checkSPTypePol :: (MonadTCM tcm) => Name -> Int -> (Polarity, Type) -> tcm ()
    checkSPTypePol nmConstr idx (SPos, tp) =
      do
        (ctx1, t1) <- unfoldPi tp
        when (isFree idx ctx1) $ error $ "inductive type not strictly positive: " ++ show nmConstr
        case unApp t1 of
          (Bound i,  args) -> do
            when (isFree (idx + size ctx1) args) $ error $ "inductive type appears as argument: " ++ show nmConstr
            when (i /= idx + size ctx1) $ error $ "I don't think this is possible: expected " ++ show (idx + size ctx1) ++ " but found " ++ show i
          (Ind an nmInd parsInd, argsInd) -> do
            ind <- getGlobal nmInd
            let pols = indPol ind
            mapM_ (checkSPTypePol nmConstr (idx+size ctx1)) (zip pols parsInd)
          _ -> error $ "not valid type " ++ show nmConstr
    checkSPTypePol nmConstr idx (pol, tp) =
      when (isFree idx tp) $ error ("not strictly positive in " ++ show nmConstr)
