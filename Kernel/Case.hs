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

import Utils.Misc
import Utils.Pretty

inferCase :: (MonadTCM tcm) => A.CaseExpr -> tcm (Term, Type)
inferCase ccc@(A.CaseExpr _ arg asNm caseIn whSubst (Just ret) branches) =
    do -- Typecheck the argument
       traceTCM_ ["Typechecking case:\n", show $ prettyPrint ccc]
       traceTCM_ ["infer argument of case ", show arg]
       (arg', tpArg) <- infer arg
       traceTCM_ ["inferred argument and type ", show arg', "\n : ", show tpArg]
       -- Check that the type is an inductive type and get pars and indices
       (nmInd, (pars, inds)) <- getInductiveType tpArg
       traceTCM_ ["casein ", show caseIn]
       (caseIn',ctx) <- checkCaseIn caseIn nmInd pars inds
       let Subst sg = getSubst (ctxReverse ctx)
           sg' = map (\(m,(n,t)) -> (n - m,t)) $ zip [0..] sg
           caseCtx = mkCaseBinds asNm nmInd pars tpArg caseIn'
       traceTCM_ ["inferred casein \n", show caseIn']
       e <- ask
       traceTCM_ ["Binds for ret ", show $ caseCtx, "\n in env\n", show e]
       traceTCM_ ["Infer type of ret ", show ret, "\nin context ", show $ (mkCaseBinds asNm nmInd pars tpArg caseIn')]
       (ret', sort) <- pushCtx caseCtx $ infer ret
       traceTCM_ ["Inferred ret ", show ret', "\n of type ", show sort]
       _ <- isSort sort
       traceTCM_ ["inferred case ", show $ Case (CaseTerm arg' nmInd asNm caseIn' ret' [])]
       traceTCM_ ["subst to apply ", show sg']

       -- Check branches
       traceTCM_ ["\n\nBRANCHES "]
       allConstrs <- listConstructors nmInd
       let posConstrs = map A.brName branches
           negConstrs = allConstrs \\ posConstrs
       traceTCM_ ["+++ : ", show posConstrs, "\n_|_ :", show negConstrs]

       -- Checking positive branches
       posBranches <- mapM (checkBranch asNm nmInd pars caseIn' ret') branches

       -- Checking negative branches
       _ <- mapM (checkImpossBranch pars caseIn') negConstrs

       -- traceTCM_ ["branches checked!"]

       -- traceTCM_ ["return type ", show ret]
       -- traceTCM_ ["return type ", show ret', "   \nsubst ", show sg']
       -- e <- pushCtx caseCtx $ ask
       -- e' <- ask
       -- traceTCM_ ["env ", show e]
       -- traceTCM_ ["\n\nreturn type  ", show $ (subst arg' ret')]
       -- traceTCM_ ["\n\nreturn type  ", show (foldr (\(k,t) r -> substN k t r) ret' sg'), "\n in context ", show e']

       -- Building return type
       let ret1 = ifMaybe_ asNm (subst arg') ret'
           ret2 = unfoldCtx ctx ret'
       -- traceTCM_ ["ret2 ", show ret2]

       -- Final result
       return (Case (CaseTerm arg' nmInd asNm caseIn' ret' posBranches),
               ret2)
    where checkCaseIn :: (MonadTCM tcm) => Maybe A.CaseIn -> Name -> [Term] -> [Term] -> tcm (Maybe (I.CaseIn), Context)
          checkCaseIn Nothing _ _ _ = return (Nothing, empCtx)
          checkCaseIn (Just c) nmInd pars inds
            | A.inInd c /= nmInd = error "wrong inductive type in case"
            | otherwise = do i <- getGlobal nmInd
                             (inBind', _) <- inferBinds $ A.inBind c
                             e <- ask
                             traceTCM_ ["env : ", show e]
                             traceTCM_ ["check indices in ", show (indIndices i), "\n", show pars, "\n", show (foldr subst (indIndices i) pars), "\n against ", show (A.inArgs c)]
                             inArgs' <- pushCtx inBind' $
                                        checkList (A.inArgs c)
                                        (foldr subst (indIndices i) pars)
                             traceTCM_ ["checked indices ", show inArgs']
                             traceTCM_ ["checked inBind ", show inBind']
                             let liftInds = map (I.lift (ctxLen inBind') 0) inds
                             traceTCM_ ["calling unify between ", show liftInds, "\nand ", show inArgs']
                             (bs'', p, ks) <- unifyPos inBind' (zip liftInds inArgs') [0..ctxLen inBind'-1]
                             traceTCM_ ["Unified! ", show bs'', "\n  ", show ks]
                             when (length ks > 0) $ error "variables not unified in"
                             return (Just (I.CaseIn inBind' nmInd inArgs'),
                                     bs'')
          getBindsCaseIn Nothing = empCtx
          getBindsCaseIn (Just c) = inBind c
          mkCaseBinds :: Maybe Name -> Name -> [Term] -> Type -> Maybe CaseIn -> Context
          mkCaseBinds Nothing _ _ _ Nothing = empCtx
          mkCaseBinds Nothing _ _ _ (Just c) = inBind c
          mkCaseBinds (Just x) _ _ tpArg Nothing = Bind x tpArg <| empCtx
          mkCaseBinds (Just x) nmInd pars _ (Just c) =
            Bind x (mkApp (Ind Empty nmInd) (pars ++ inArgs c)) <| ctxReverse (inBind c)
          getInductiveType t =
             do t' <- whnf t
                case t' of
                  App (Ind _ i) args ->
                    do Inductive tpPars _ _ _ _ <- getGlobal i -- matching should not fail
                       return (i, splitAt (ctxLen tpPars) args)
                  Ind _ i          -> return (i, ([], []))
                  _                -> error $ "case 0. not inductive type " ++ show t
          listConstructors :: (MonadTCM tcm) => Name -> tcm [Name]
          listConstructors i = indConstr <$> getGlobal i

          unfoldCtx ctx t = unfoldCtx_ 0 ctx t
          unfoldCtx_ k EmptyCtx t = t
          unfoldCtx_ k (ExtendCtx (Bind _ _) ctx) t = unfoldCtx_ (k+1) ctx t
          unfoldCtx_ k (ExtendCtx (LocalDef _ u _) ctx) t =
            unfoldCtx_ k ctx (subst (I.lift k 0 u) t)

checkBranch :: (MonadTCM tcm) =>
               Maybe Name -> Name -> [Term] -> Maybe CaseIn -> Type -> A.Branch -> tcm Branch
checkBranch asNm nmInd pars caseIn' ret'
  (A.Branch _ nmConstr idConstr nmArgs body whSubst) =
    do (Constructor _ _ _ tpArgs inds) <- getGlobal nmConstr
       -- type of branch = Π Δ_i *. P us_i * (C ps dom(Δ_i))
       let tpArgs' = renameCtx (foldr subst tpArgs pars) nmArgs -- renameBinds (foldr subst tpArgs pars) nmArgs
           inds'   = foldr subst inds pars
           Just caseIn'' = caseIn'
           whDom = case whSubst of
                     Just ws -> map A.assgnBound (A.unSubst ws)
                     Nothing -> []
           numArgs = ctxLen tpArgs'
       traceTCM_ ["where branch ", show whSubst, "\ncontext ", show (inBind caseIn'' +: tpArgs')]
       (permCtx, perm, ks) <- unifyPos (inBind caseIn'' +: tpArgs') (zip (map (I.lift numArgs 0) (inArgs caseIn'')) inds') ([numArgs..numArgs+ctxLen (inBind caseIn'')-1] ++ whDom)
       when (length ks > 0) $ error $ "variables not unified in branch " ++ show idConstr
       traceTCM_ ["\nUnify ", show nmConstr, "\n", show permCtx, "\nperm: ", show perm, "  rest: ", show ks]
       let constrArg = applyPerm perm $ Constr nmConstr (nmInd, idConstr) pars (localDom numArgs)
           ret2 = case asNm of
                    Just x -> subst constrArg ret'
                    Nothing -> ret'
           ret3 = applyPerm perm $ I.lift numArgs 0 ret2
       traceTCM_ ["checking body after perm  ", show (prettyPrint (applyPerm perm body)), "\n\nbefore perm: ", show (prettyPrint body)]
       ret3'' <- pushCtx permCtx $ reify ret3
       traceTCM_ ["against type ", show (prettyPrint ret3''), "\nbefore perm: ", show ret2, "\nlifted by ", show numArgs, " : ", show $ I.lift numArgs 0 ret2]
       e <- (pushCtx permCtx $ ask) >>= reify
       traceTCM_ ["in context ", show (prettyPrint (A.Pi noRange e (A.Sort noRange Prop)))]
       body' <- pushCtx permCtx $ check (applyPerm perm body) ret3
       -- TODO: check where substitution
       traceTCM_ ["checked body ", show body']
       return $ Branch noName idConstr nmArgs body' Nothing


localDom :: Int -> [Term]
localDom 0 = []
localDom (k+1) = Bound k : localDom k



-- | checkImpossBranch nmConstr pars caseIn
--   Does not return any value, but throws an exception if unification fails
checkImpossBranch :: (MonadTCM tcm) =>
                     [Term] -> Maybe CaseIn -> Name -> tcm ()
checkImpossBranch pars caseIn' nmConstr =
    do (Constructor _ _ _ tpArgs inds) <- getGlobal nmConstr
       -- type of branch = Π Δ_i *. P us_i * (C ps dom(Δ_i))
       let tpArgs' = foldr subst tpArgs pars
           inds'   = foldr subst inds pars
           Just caseIn'' = caseIn'
           numArgs = ctxLen tpArgs'
           ctx = inBind caseIn'' +: tpArgs'
           eqs = zip (map (I.lift numArgs 0) (inArgs caseIn'')) inds'
           freeVars = [0..ctxLen (inBind caseIn'') + numArgs - 1]
       unifyNeg ctx eqs freeVars
       traceTCM_ ["Impossible branch ", show nmConstr]
