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

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses
  #-}

module Kernel.Case where

import Data.List
import Data.Functor
import Control.Monad.Reader

import qualified Control.Exception as E

import Syntax.Common
import Syntax.Position
import Syntax.Internal as I
import Syntax.InternaltoAbstract
import Syntax.Size
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Unification
import Kernel.Permutation
import Kernel.Whnf
import {-# SOURCE #-} Kernel.TypeChecking

import Utils.Fresh
import Utils.Misc
import Utils.Pretty
import Utils.Sized

inferCase :: (MonadTCM tcm) => A.CaseExpr -> tcm (Term, Type)
inferCase (A.CaseExpr rg arg asNm caseIn whSubst (Just ret) branches) = do

  -- Typecheck the argument
  (arg', tpArg) <- infer arg

  -- Check that the type of the argument is an inductive type and get parameters
  -- and family indices
  (kind, sta, nmInd, (pars, inds)) <- getInductiveType tpArg

  -- Force the stage of the argument to be a successor
  sta1 <- fresh
  case kind of
    I   -> addStageConstraints (sta <<= (Size (Hat (Svar sta1))))
    CoI -> addStageConstraints (Size (Hat (Svar sta1)) <<= sta)

  -- Check the family specification. Unify with the family of the inductive type
  -- The resulting unification is used to type-check the return type
  (caseIn',ctx) <- checkCaseIn caseIn nmInd pars inds

  -- Context for the return type
  let caseCtx = mkCaseBinds asNm nmInd pars tpArg caseIn'

  -- Check the return type and check that its type is a sort
  (ret', sort) <- pushCtx caseCtx $ infer ret
  _ <- isSort sort

  -- Check branches
  -- Find possible and impossible branches
  allConstrs <- listConstructors nmInd
  let posConstrs = map A.brName branches
      negConstrs = allConstrs \\ posConstrs
  -- traceTCM_ ["+++ : ", show posConstrs, "\n_|_ :", show negConstrs]

  -- Checking possible
  posBranches <- mapM (checkBranch (Size (Svar sta1)) asNm nmInd pars caseIn' ret') branches

  -- Checking impossible branches
  _ <- mapM (checkImpossBranch pars caseIn') negConstrs

  -- Building return type
  let -- Substitute the argument in the type, if it exists
      ret1 = ifMaybe_ asNm (subst arg') ret'
      -- Substitute all the defined variables in the context ctx returned by
      -- unifying the CaseIn family specification
      ret2 = unfoldCtx ctx ret1

  
  -- traceTCM_ ["checked case ", show rg, "\nof type", show ret2]
  -- Final result
  return (Case (CaseTerm arg' nmInd asNm caseIn' (eraseSize ret') posBranches), 
          ret2)

    where
      checkCaseIn :: (MonadTCM tcm) =>
                     Maybe A.CaseIn -> Name -> [Term] -> [Term] ->
                     tcm (Maybe (I.CaseIn), Context)
      checkCaseIn Nothing _ _ _ = return (Nothing, empCtx)
      checkCaseIn (Just c) nmInd pars inds
        | A.inInd c /= nmInd = error "wrong inductive type in case"
        | otherwise = do
          i <- getGlobal nmInd
          (inBind', _) <- inferBinds $ A.inBind c
          inArgs' <- pushCtx inBind' $ checkList (A.inArgs c) (foldr subst (indIndices i) pars)
          let liftInds = map (I.lift (size inBind') 0) inds
          (bs'', p, ks) <- unifyPos inBind' (zip liftInds inArgs') [0..size inBind'-1]
          when (length ks > 0) $ error "variables not unified in"
          return (Just (I.CaseIn inBind' nmInd inArgs'), bs'')

      mkCaseBinds :: Maybe Name -> Name -> [Term] -> Type -> Maybe CaseIn -> Context
      mkCaseBinds Nothing _ _ _ Nothing = empCtx
      mkCaseBinds Nothing _ _ _ (Just c) = inBind c
      mkCaseBinds (Just x) _ _ tpArg Nothing = mkBind x tpArg <| empCtx
      mkCaseBinds (Just x) nmInd pars _ (Just c) =
         inBind c |> mkBind x (mkApp (Ind Empty nmInd) (map (I.lift (size c) 0) pars ++ inArgs c))

      getInductiveType t = do
        t' <- whnF t
        case t' of
          App (Ind a i) args -> do
            Inductive k tpPars _ _ _ _ <- getGlobal i -- matching should not fail
            return (k, a, i, splitAt (size tpPars) args)
          Ind a i          -> do
            Inductive k tpPars _ _ _ _ <- getGlobal i -- matching should not fail
            return (k, a, i, ([], []))
          _                -> error $ "case 0. not inductive type " ++ show t

      listConstructors :: (MonadTCM tcm) => Name -> tcm [Name]
      listConstructors i = indConstr <$> getGlobal i

      unfoldCtx ctx t = unfoldCtx_ 0 ctx t
      unfoldCtx_ k EmptyCtx t = t
      unfoldCtx_ k (ExtendCtx (Bind _ _ _ Nothing) ctx) t = unfoldCtx_ (k+1) ctx t
      unfoldCtx_ k (ExtendCtx (Bind _ _ _ (Just u)) ctx) t =
        unfoldCtx_ k ctx (subst (I.lift k 0 u) t)


inferCase (A.CaseExpr _ _ _ _ _ Nothing _) =
  error "Case with no return type not handled yet. Add a return type"



checkBranch :: (MonadTCM tcm) =>
               Annot -> Maybe Name -> Name -> [Term] -> Maybe CaseIn -> Type -> A.Branch -> tcm Branch
checkBranch sta asNm nmInd pars caseIn' ret'
  (A.Branch _ nmConstr idConstr nmArgs body whSubst) = do

  (Constructor _ _ _ tpArgs _ inds) <- getGlobal nmConstr
  
  -- TODO: replace star for the appropiate stage
  let replStage x = if x == Star then sta else x

  let tpArgs' = I.lift (size inCtx) 0 $ renameCtx (foldr subst (modifySize replStage tpArgs) pars) nmArgs
      numPars = length pars
      numArgs = size tpArgs'
      inds' = substList (numArgs + numPars - 1) pars inds
      inCtx = maybe empCtx inBind caseIn'
      inFam = maybe [] inArgs caseIn'
      whDom = case whSubst of
                Just ws -> map A.assgnBound (A.unSubst ws)
                Nothing -> []

  (permCtx, perm, ks) <- unifyPos (inCtx +: tpArgs') (zip (map (I.lift numArgs 0) inFam) inds') ([numArgs..numArgs+size inCtx-1] ++ whDom)

  when (length ks > 0) $ error $ "variables not unified in branch " ++ show idConstr

  let constrArg = applyPerm perm $ Constr empCtx nmConstr (nmInd, idConstr) pars (localDom numArgs)
      ret2 = ifMaybe_ asNm (subst constrArg) ret'
      ret3 = applyPerm perm $ I.lift numArgs 0 ret2

  -- Check body
  body' <- pushCtx permCtx $ check (applyPerm perm body) ret3

  -- TODO: check where substitution
  -- return final result
  return $ Branch noName idConstr nmArgs body' Nothing


localDom :: Int -> [Term]
localDom 0 = []
localDom k = Bound (k-1) : localDom (k-1)



-- | checkImpossBranch nmConstr pars caseIn
--   Does not return any value, but throws an exception if unification fails
checkImpossBranch :: (MonadTCM tcm) =>
                     [Term] -> Maybe CaseIn -> Name -> tcm ()
checkImpossBranch pars caseIn' nmConstr = do
  (Constructor _ _ _ tpArgs _ inds) <- getGlobal nmConstr

  -- TODO: replace star for the appropiate stage
  let replStage x = if x == Star then (Size Infty) else x

  let tpArgs' = foldr subst (modifySize replStage tpArgs) pars
      inds'   = foldr subst inds pars
      numArgs = size tpArgs'
      ctx = maybe empCtx inBind caseIn' +: tpArgs'
      eqs = zip (map (I.lift numArgs 0) (maybe [] inArgs caseIn')) inds'
      freeVars = [0..size (maybe empCtx inBind caseIn') + numArgs - 1]
  unifyNeg ctx eqs freeVars
  -- traceTCM_ ["Impossible branch ", show nmConstr]
