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

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CICwf.TypeChecking.Case where

import           Control.Monad.Reader

import           Data.Functor
import           Data.List
import           Data.Set            (Set)
import qualified Data.Set            as Set

import qualified CICwf.Syntax.Abstract           as A
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           as I
import           CICwf.Syntax.Position
import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.Match
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors
import {-# SOURCE #-} CICwf.TypeChecking.TypeChecking
import           CICwf.TypeChecking.Whnf

import           CICwf.Utils.Fresh
import           CICwf.Utils.Misc
import           CICwf.Utils.Sized

inferCase :: (MonadTCM tcm) => A.CaseExpr -> tcm (Term, Type)
inferCase (A.CaseExpr rg caseki arg asNm indspec (Just ret) branches) = do

  -- Typecheck the argument
  (arg', tpArg) <- infer arg

  -- Check that the type of the argument is an inductive type and get parameters
  -- and family indices
  (kind, sta, nmInd, (pars, inds)) <- getInductiveType tpArg

  -- Force the stage of the argument to be a successor
  (caseki', sta1) <- case (kind, caseki) of
    (I, CaseKind)       -> return (CaseKind, sta)
    (CoI, CocaseKind _) -> do
      sta1 <- freshStage (range arg)
      addWfConstraint (hat (mkAnnot sta1)) sta
      return (CocaseKind (mkAnnot sta1), mkAnnot sta1)
    (_, _) -> typeError (range arg)
              $ GenericError "Expected (co)inductive type in case argument"

  -- Check the family specification
  (indicesPat, indicesCtx) <- checkCaseIndices indspec nmInd pars inds

  -- Context for the return type
  returnTypeCtx <- mkCaseBinds asNm nmInd sta1 pars indicesCtx

  -- Check the return type and check that its type is a sort
  (ret', s) <- pushCtx returnTypeCtx $ inferType ret

  -- Check branches
  -- Find possible and impossible branches
  allConstrs <- listConstructors nmInd
  let posConstrs = map A.brName branches
      negConstrs = allConstrs \\ posConstrs

  -- Checking possible
  posBranches <- mapM (checkBranch caseki' sta1 asNm nmInd pars indicesPat ret') branches

  -- Checking impossible branches
  _ <- mapM (checkImpossibleBranch sta1 pars indicesPat) negConstrs

  let instReturnType = substList0 (inds ++ [arg']) ret'
  -- Final result
  return (Case (CaseTerm caseki' arg' nmInd asNm nmInd pars indicesPat ret'
                posBranches), instReturnType)


inferCase (A.CaseExpr rg _ _ _ _ Nothing _) =
  notImplemented rg ("Case with no return type not handled yet." ++
                     "Add a return type")


getInductiveType :: (MonadTCM tcm) => Term ->
                    tcm (InductiveKind, Annot, Name, ([Term], [Term]))
getInductiveType t = do
  t' <- whnf t
  case t' of
    App (Ind a False i pars) args -> do
      i'@(Inductive {}) <- getGlobal i -- matching should not fail
      return (indKind i', a, i, (pars, args))
    Ind a False i pars       -> do
      i'@(Inductive {}) <- getGlobal i -- matching should not fail
      return (indKind i', a, i, (pars, []))
    _                -> error "case 0. not inductive type "


listConstructors :: (MonadTCM tcm) => Name -> tcm [Name]
listConstructors i = indConstr <$> getGlobal i


-- mkCaseBinds asNm nmInd stage pars indicesCtx
mkCaseBinds :: (MonadTCM tcm) => Name -> Name -> Annot -> [Term]
               -> Context -> tcm Context
mkCaseBinds asNm nmInd stage pars indicesCtx = do
  let indLen = size indicesCtx
  let asTp = mkApp (Ind stage False nmInd (I.lift indLen 0 pars))
             (reverse (take indLen (map Bound [0..])))

  return (ctxPush indicesCtx (Bind asNm (mkArg asTp) Nothing))


checkCaseIndices :: (MonadTCM tcm) =>
               Maybe A.IndicesSpec -> Name -> [Term] -> [Term] ->
               tcm (Pattern, Context)
checkCaseIndices Nothing nmInd pars inds = do
  indDef <- getGlobal nmInd
  return (take len (repeat (PatternVar noName)), getIndIndices indDef pars)
  where
    len = size inds
checkCaseIndices (Just c) nmInd pars inds
  | A.indspecType c /= nmInd = error "wrong inductive type in case"
  | otherwise = do
    indDef <- getGlobal nmInd
    let indicesCtx = getIndIndices indDef pars
    let indicesPattern = drop (size pars) (A.indspecArgs c)
    (pat, ctx) <- checkPattern indicesPattern indicesCtx

    -- Check that the pattern is convertible with the indices of the argument
    -- I.e. pat ~ inds
    checkIndicesConv pat inds
    return (pat, ctx)
      where
        checkIndicesConv [] [] = return ()
        checkIndicesConv (PatternVar _:ps) (_:ts) = checkIndicesConv ps ts
        checkIndicesConv (PatternDef _ u:ps) (t:ts) = do
          unlessM (u `conv` t) $ typeError (range c) $ NotConvertible u t
          checkIndicesConv ps ts


checkBranch :: (MonadTCM tcm) => CaseKind Annot -> Annot -> Name -> Name -> [Term] -> Pattern
               -> Type -> A.Branch -> tcm Branch
checkBranch caseki costa asNm nmInd pars indicesPat returnType
  (A.Branch rg Nothing nmConstr idConstr branchPat body) = do

  constr@(Constructor _ _ cPars tpArgs _ inds) <- getGlobal nmConstr
  (sta, brsize, wfdecl) <- case caseki of
    CaseKind -> do
      km <- freshSizeName (mkName "k")
      return (mkAnnot km, Just km, pushWfDecl km costa)
    CocaseKind _ -> return (costa, Nothing, id)

  -- Check that pattern is well typed
  let constrCtx = getConstrContext constr pars sta

  (branchPat', branchCtx) <- checkPattern branchPat constrCtx

  -- Match constructor indices against argument indices
  let indices' = getConstrIndices constr pars
                 (reverse (take (size branchPat') (map Bound [0..])))
  let argsToMatch = map fst (filter (\ (_,x) -> isPatternDef x) (zip (reverse (take (size branchPat') [0..])) branchPat'))

  (ctx0, rest) <- matchPos constrCtx (zip indices' (lift0 (size branchPat') indicesPat)) argsToMatch

  -- Check that context returned by matching is convertible with the pattern
  unlessM (ctx0 `conv` branchCtx) $
    typeError (range branchPat) $ BranchPatternNotConvertible ctx0 branchCtx

  let constrIndices = getConstrIndices constr pars (boundArgs (size branchPat))
      numArgs = size (constrArgs constr)
      constrArg = Intro sta (mkApp (Constr nmConstr (nmInd, idConstr) pars) (localDom numArgs))
      instReturnType =
        substList0
        (constrIndices ++ [constrArg]) (I.lift (size branchPat) (size indicesPat + 1) returnType)


  body' <- wfdecl $ pushCtx branchCtx $ check body instReturnType
  case brsize of
    Just km -> addWfIndependent km (Set.elems (fAnnot body'))
    Nothing -> return ()
  return $ Branch brsize nmConstr idConstr branchPat' body'


localDom :: Int -> [Term]
localDom 0 = []
localDom k = Bound (k-1) : localDom (k-1)


-- | checkImpossBranch nmConstr pars caseIn
--   Does not return any value, but throws an exception if unification fails
checkImpossibleBranch :: (MonadTCM tcm) =>
                     Annot -> [Term] -> Pattern -> Name -> tcm ()
checkImpossibleBranch sta pars indicesPat nmConstr = do
  constr@(Constructor {}) <- getGlobal nmConstr

  -- Check that pattern is well typed
  let constrCtx = getConstrContext constr pars sta
  let numArgs = size (constrArgs constr)
  -- Match constructor indices against argument indices
  let indices' = getConstrIndices constr pars (boundArgs numArgs)

  let argsToMatch = take numArgs [0..]

  let eqs = (zip indices' (lift0 numArgs indicesPat))
  matchNeg constrCtx eqs argsToMatch
