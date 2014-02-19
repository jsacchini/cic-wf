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

module CICminus.TypeChecking.Case where

import           Control.Monad.Reader

import           Data.Functor
import           Data.List

import qualified CICminus.Syntax.Abstract           as A
import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal           as I
import           CICminus.Syntax.Position
import           CICminus.Syntax.Size
import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.Match
-- import           CICminus.TypeChecking.Permutation
import           CICminus.TypeChecking.PrettyTCM    hiding ((<>))
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.TCMErrors
import {-# SOURCE #-} CICminus.TypeChecking.TypeChecking
-- import           CICminus.TypeChecking.Unification
import           CICminus.TypeChecking.Whnf

import           CICminus.Utils.Fresh
import           CICminus.Utils.Misc
import           CICminus.Utils.Sized

inferCase :: (MonadTCM tcm) => A.CaseExpr -> tcm (Term, Type)
inferCase (A.CaseExpr rg arg asNm indspec (Just ret) branches) = do

  -- Typecheck the argument
  traceTCM 30 $ hsep [ text "CASE ARGUMENT from", prettyTCM arg ]
  (arg', tpArg) <- infer arg
  traceTCM 30 $ (hsep [ text "CASE ARGUMENT to", prettyTCM arg' ]
                 $$ hsep [ text "of type", prettyTCM tpArg ])

  -- Check that the type of the argument is an inductive type and get parameters
  -- and family indices
  (kind, sta, nmInd, (pars, inds)) <- getInductiveType tpArg
  traceTCM 30 $ hsep [ text "CASE INDUCTIVE TYPE", prettyTCM nmInd ]

  -- Force the stage of the argument to be a successor
  sta1 <- freshStage (range arg)
  case kind of
    I   -> addStageConstraints (hat (mkAnnot sta1) <<= sta)
    CoI -> addStageConstraints (sta <<= hat (mkAnnot sta1))

  -- Check the family specification
  traceTCM 30 $ hsep [ text "CASE IN from", prettyTCM indspec ]
  (indicesPat, indicesCtx) <- checkCaseIndices indspec nmInd pars inds
  traceTCM 30 $ hsep [ text "CASE IN to"
                     , prettyTCM indicesCtx ]

  -- Context for the return type
  returnTypeCtx <- mkCaseBinds asNm nmInd (mkAnnot sta1) pars indicesCtx
  traceTCM 30 $ vcat [ text "full return context"
                       <+> prettyTCM returnTypeCtx
                     , text "in ctx   " <+> (ask >>= prettyTCM) ]

  -- Check the return type and check that its type is a sort
  traceTCM 30 $ hsep [ text "CASE RETURN from", pushCtx returnTypeCtx $ prettyTCM ret ]
  (ret', s) <- pushCtx returnTypeCtx $ infer ret
  pushCtx returnTypeCtx $
    traceTCM 30 $ vcat [ text "CASE RETURN to" <+> prettyTCM ret'
                       , text "of type " <+>  prettyTCM s
                       , text "in ctx" <+> (ask >>= prettyTCM) ]
  _ <- isSort (range ret) s

  -- Check branches
  -- Find possible and impossible branches
  allConstrs <- listConstructors nmInd
  let posConstrs = map A.brName branches
      negConstrs = allConstrs \\ posConstrs
  traceTCM 30 $ hsep [text "+++ : ", prettyTCM posConstrs
                     , text "\n_|_ :", prettyTCM negConstrs]

  -- Checking possible
  posBranches <- mapM (checkBranch (mkAnnot sta1) asNm nmInd pars indicesPat ret') branches

  traceTCM 30 $ hsep [ text "IMPOSSIBLE branches", text (show negConstrs) ]
  -- Checking impossible branches
  _ <- mapM (checkImpossibleBranch (mkAnnot sta1) pars indicesPat) negConstrs

  let instReturnType = substList0 (inds ++ [arg']) ret'

  traceTCM 50 $ text "checked case " <+> prettyTCM rg
    <+> text "of type" <+> prettyTCM instReturnType
--   -- Final result
  return (Case (CaseTerm arg' nmInd asNm nmInd (map eraseSize pars) indicesPat (eraseSize ret') posBranches), instReturnType)


inferCase (A.CaseExpr rg _ _ _ Nothing _) =
  notImplemented rg ("Case with no return type not handled yet." ++
                     "Add a return type")


getInductiveType :: (MonadTCM tcm) => Term ->
                    tcm (InductiveKind, Annot, Name, ([Term], [Term]))
getInductiveType t = do
  t' <- whnf t
  case t' of
    App (Ind a i pars) args -> do
      i'@(Inductive {}) <- getGlobal i -- matching should not fail
      return (indKind i', a, i, (pars, args))
    Ind a i pars       -> do
      i'@(Inductive {}) <- getGlobal i -- matching should not fail
      return (indKind i', a, i, (pars, []))
    _                -> error $ "case 0. not inductive type " -- ++ show t


listConstructors :: (MonadTCM tcm) => Name -> tcm [Name]
listConstructors i = indConstr <$> getGlobal i


-- mkCaseBinds asNm nmInd stage pars indicesCtx
mkCaseBinds :: (MonadTCM tcm) => Name -> Name -> Annot -> [Term]
               -> Context -> tcm Context
mkCaseBinds asNm nmInd stage pars indicesCtx = do
  let indLen = size (indicesCtx)
  let asTp = mkApp (Ind stage nmInd (I.lift indLen 0 pars))
             (reverse (take indLen (map Bound [0..])))

  return (ctxPush indicesCtx (Bind asNm (mkArg asTp) Nothing))


checkCaseIndices :: (MonadTCM tcm) =>
               Maybe A.IndicesSpec -> Name -> [Term] -> [Term] ->
               tcm (Pattern, Context)
checkCaseIndices Nothing nmInd pars inds = do
  indDef <- getGlobal nmInd
  return $ (take len (repeat (PatternVar noName)), getIndIndices indDef pars)
  where
    len = size inds
checkCaseIndices (Just c) nmInd pars inds
  | A.indspecType c /= nmInd = error "wrong inductive type in case"
  | otherwise = do
    indDef <- getGlobal nmInd
    let indicesCtx = getIndIndices indDef pars
    let indicesPattern = drop (size pars) (A.indspecArgs c)
    traceTCM 30 $ vcat [ text "check IN context" <+> prettyTCM c
                       , text "against" <+> prettyTCM indicesCtx ]
    (pat, ctx) <- checkPattern indicesPattern indicesCtx

    -- Check that the pattern is convertible with the indices of the argument
    -- I.e. pat ~ inds
    checkIndicesConv pat inds
    return (pat, ctx)
      where
        checkIndicesConv [] [] = return ()
        checkIndicesConv (PatternVar _:ps) (_:ts) = checkIndicesConv ps ts
        checkIndicesConv (PatternDef _ u:ps) (t:ts) = do
          unlessM (u `conv` t) $ throwNotConvertible (Just (range c)) u t
          checkIndicesConv ps ts


checkBranch :: (MonadTCM tcm) => Annot -> Name -> Name -> [Term] -> Pattern
               -> Type -> A.Branch -> tcm Branch
checkBranch sta asNm nmInd pars indicesPat returnType
  (A.Branch rg nmConstr idConstr branchPat body) = do

  constr@(Constructor _ _ cPars tpArgs _ inds) <- getGlobal nmConstr
  traceTCM 30 $ (text "Checking branch in context:"
                 <+> (ask >>= prettyTCM)
                 $$ text "parameters: " <+> prettyTCM pars
                 $$ text "stage: " <+> text (show sta)
                 $$ text "constructor args:" <+> pushCtx cPars (prettyTCM (constrArgs constr)))
  -- Check that pattern is well typed
  let constrCtx = getConstrContext constr pars sta
  traceTCM 30 $ vcat [ text "pattern" <+> prettyTCM branchPat
                     , text "against context" <+>  prettyTCM constrCtx ]

  (branchPat', branchCtx) <- checkPattern branchPat constrCtx
  traceTCM 30 $ vcat [ text "checked pattern"
                       <+> prettyTCM (branchPat', branchCtx) ]

  -- Match constructor indices against argument indices
  let indices' = getConstrIndices constr pars
                 (reverse (take (size branchPat') (map Bound [0..])))
  let argsToMatch = map fst (filter (\ (_,x) -> isPatternDef x) (zip (reverse (take (size branchPat') [0..])) branchPat'))
  pushCtx constrCtx
    $ traceTCM 30 $ vcat [ text "indices" <+> prettyTCM indices'
                         , text "against" <+> prettyTCM (lift0 (size branchPat') indicesPat)
                         , text "in Ctx" <+> (ask >>= prettyTCM) ]

  (ctx0, rest) <- matchPos constrCtx (zip indices' (lift0 (size branchPat') indicesPat)) argsToMatch
  traceTCM 30 $ vcat [ text "Matched context " <+> prettyTCM ctx0
                     , text "rest" <+> prettyTCM rest ]

  -- Check that context returned by matching is convertible with the pattern
  unlessM (ctx0 `conv` branchCtx) $
    throwBranchPatternNotConvertible (range branchPat) ctx0 branchCtx

  let constrIndices = getConstrIndices constr pars (boundArgs (size branchPat))
  let instReturnType =
        substList0
        (constrIndices ++ [(Constr nmConstr
                           (nmInd, idConstr) pars)]) (lift0 (size branchPat) returnType)

  pushCtx branchCtx $ traceTCM 30 $ vcat [ hsep [ text "Return type for branch", prettyTCM nmConstr
                            , text ":", prettyTCM instReturnType ]
                     , text "in context:" <+> (ask >>= prettyTCM) ]

  body' <- pushCtx branchCtx $ check body instReturnType
  return $ Branch nmConstr idConstr branchPat' body'

-- | checkImpossBranch nmConstr pars caseIn
--   Does not return any value, but throws an exception if unification fails
checkImpossibleBranch :: (MonadTCM tcm) =>
                     Annot -> [Term] -> Pattern -> Name -> tcm ()
checkImpossibleBranch sta pars indicesPat nmConstr = do
  constr@(Constructor {}) <- getGlobal nmConstr

  traceTCM 30 $ hsep [ text "Checking impossible branch", prettyTCM nmConstr ]
  -- Check that pattern is well typed
  let constrCtx = getConstrContext constr pars sta
  let numArgs = size (constrArgs constr)
  -- Match constructor indices against argument indices
  let indices' = getConstrIndices constr pars (boundArgs numArgs)

  let argsToMatch = take numArgs [0..]

  let eqs = (zip indices' (lift0 numArgs indicesPat))
  matchNeg constrCtx eqs argsToMatch
