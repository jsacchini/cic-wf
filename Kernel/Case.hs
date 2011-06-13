{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, CPP
  #-}

module Kernel.Case where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader
import qualified Data.Foldable as Fold

import Syntax.Common
import Syntax.Internal
import Syntax.Size
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import {-# SOURCE #-} Kernel.TypeChecking


inferCase :: (MonadTCM tcm) => A.CaseExpr -> tcm (Term, Type)
inferCase (A.CaseExpr _ arg Nothing Nothing Nothing (Just ret) branches) =
    do (arg', tpArg) <- infer arg
       (nmInd, (pars, inds)) <- getInductiveType tpArg
       Inductive _ _ tpInds _ _ <- getGlobal nmInd
       let tpArgGen = mkApp (Ind Empty nmInd) (pars ++ dom tpInds)
       (ret', tpRet) <- infer ret
       checkReturnType tpRet (tpInds |> Bind (Id "x") tpArgGen)
       branches' <- checkBranches nmInd ret' pars branches
       let tpCase = mkApp ret' $ inds ++ [arg']
       tpCase' <- whnf tpCase
       return (Case $ CaseTerm arg' nmInd ret' branches', tpCase')
         where
           getInductiveType t =
             do t' <- whnf t
                case t' of
                  App (Ind _ i) args ->
                    do Inductive tpPars _ _ _ _ <- getGlobal i -- matching should not fail
                       return (i, splitAt (ctxLen tpPars) args)
                  Ind _ i          -> return (i, ([], []))
                  _                -> error $ "case 0. not inductive type " ++ show t
           checkReturnType t bs =
             do t' <- whnf t
                case t' of
                  Pi bs' u -> do b <- conversion bs bs'
                                 unless b $ error "case 1"
                                 _ <- isSort u
                                 return ()
                  _        -> error "case 2"
inferCase _ = error "To be implemented (infer of Case)"

-- | 'checkBranches' @nmInd tpRet pars branches@ typechecks @branches@, where
--
--   * @nmInd@ is the name of the inductive type
--   * @tpRet@ is the return type of the whole case
--   * @pars@ are the parameters of the inductive type, to be applied in all the
--     expressions
--   * @branches@ is the list of branches to typecheck
--
--   We assume that all branches belong to the same inductive type (this is
--   ensured by the scope checker).
checkBranches :: (MonadTCM tcm) =>
                 Name -> Type -> [Term] -> [A.Branch] -> tcm [Branch]
checkBranches nmInd tpRet pars = check_
  where
    check_ [] = return []
    check_ (A.Branch _ nmConstr idConstr nmArgs body whSubst: bs) =
      do (Constructor _ _ _ tpArgs inds) <- getGlobal nmConstr
         -- type of branch = Π Δ_i *. P us_i * (C ps dom(Δ_i))
         let tpArgs' = renameBinds (Fold.foldr subst tpArgs pars) nmArgs
             inds'   = foldr subst inds pars
             constr  = Constr nmConstr (nmInd, idConstr) pars (dom tpArgs')
             tpBranch = mkApp tpRet (inds' ++ [constr])
         body' <- pushCtx tpArgs' $ check body tpBranch
         bs' <- check_ bs
         return $ Branch nmConstr idConstr nmArgs body' (Just (Subst [])): bs'


------------------------------------------------------------
-- * Misc functions
------------------------------------------------------------

dom :: Context -> [Term]
dom bs = reverse $ bound 0 (ctxLen bs - 1)
  where bound :: Int -> Int -> [Term]
        bound m n = map Bound [m..n]


-- | Changes the names of binds (used to print names similar to the ones given
--   by the user.
--
--   Expects lists of the same size.
renameBinds :: Context -> [Name] -> Context
renameBinds EmptyCtx [] = EmptyCtx
renameBinds (ExtendCtx (Bind _ t) c) (x:xs) = Bind x t <| renameBinds c xs
renameBinds (ExtendCtx (LocalDef _ t1 t2) c) (x:xs) = LocalDef x t1 t2 <| renameBinds c xs
renameBinds _ _ = __IMPOSSIBLE__

