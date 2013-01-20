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

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
    FlexibleInstances, TypeSynonymInstances
  #-}

module Kernel.TypeChecking where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader

import qualified Text.PrettyPrint as PP

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.InternaltoAbstract
import Syntax.Common
import Syntax.Position
import Syntax.Size
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import Kernel.Inductive (inferInd)
import Kernel.Fix (inferFix)
import Kernel.Case (inferCase)
import Kernel.PrettyTCM
import Utils.Fresh
import Utils.Pretty

checkSort :: (MonadTCM tcm) => A.Sort -> tcm (Term, Type)
checkSort A.Prop     = do f <- fresh
                          return (Sort Prop, Sort (Type f))
checkSort (A.Type _) = do f1 <- fresh
                          f2 <- fresh
                          addTypeConstraints [(f1, f2, -1)]
                          return (Sort (Type f1), Sort (Type f2))

checkProd :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
checkProd (Type _) Prop = return Prop
checkProd Prop (Type n) = return $ Type n
checkProd (Type m) (Type n) = do traceTCM 30 $ hsep [text "check product",
                                                     prettyPrintTCM m,
                                                     prettyPrintTCM n]
                                 k <- fresh
                                 addTypeConstraints [(m, k, 0), (n, k, 0)]
                                 return $ Type k

maxSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
maxSort (Type m) Prop = return $ Type m
maxSort Prop (Type n) = return $ Type n
maxSort (Type m) (Type n) = do traceTCM 30 $ hsep [text "max sort",
                                                   prettyPrintTCM m,
                                                   prettyPrintTCM n]
                               k <- fresh
                               addTypeConstraints [(m, k, 0), (n, k, 0)]
                               return $ Type k

isSort :: (MonadTCM tcm) => Term -> tcm Sort
isSort t = do t' <- whnf t
              case t' of
                Sort s -> return s
                _      -> do xs <- ask
                             typeError $ NotSort xs t

-- We assume that in the global environment, types are normalized

inferBinds :: (MonadTCM tcm) => [A.Bind] -> tcm (Context, Sort)
inferBinds bs = inferList bs
    where inferList [] = return (empCtx, Prop)
          inferList (b:bs) = do (ctx1, s1) <- inferBind b
                                (ctx2, s2) <- pushCtx ctx1 $ inferList bs
                                s' <- maxSort s1 s2
                                return (ctx1 +: ctx2, s')
          inferBind (A.Bind _ _ [] _) = return (empCtx, Prop)
          inferBind (A.Bind rg impl (x:xs) e) = do
            (t1, r1) <- infer e
            s1 <- isSort r1
            (ctx, s2) <- pushBind (mkImplBind x impl t1) $ inferBind (A.Bind rg impl xs e)
            s' <- maxSort s1 s2
            return (mkBind x t1 <| ctx, s')
              where mkCtx [] _ _ = empCtx
                    mkCtx (y:ys) t k = mkImplBind y impl (I.lift k 0 t) <| mkCtx ys t (k + 1)


infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort r
                         t' <- check t u'
                         w <- whnf u'
                         return (t', w)
infer (A.Sort _ s) = checkSort s
infer exp@(A.Pi _ ctx t) =
  do traceTCM 30 $ hsep [text "Inferring product",
                         prettyPrintTCM exp]
     (ctx', s1) <- inferBinds ctx
     (t', r2) <- pushCtx ctx' $ infer t
     s2 <- pushCtx ctx' $ isSort r2
     s' <- checkProd s1 s2
     return (mkPi ctx' t', Sort s')
infer exp@(A.Arrow _ e1 e2) =
  do traceTCM 30 $ hsep [text "Inferring arrow",
                         prettyPrintTCM exp]
     (t1, r1) <- infer e1
     s1 <- isSort r1
     (t2, r2) <- pushType t1 $ infer e2
     s2 <- pushType t1 $ isSort r2
     s' <- checkProd s1 s2
     return (mkPi (bindNoName t1 <| empCtx) t2, Sort s')
infer (A.Bound _ _ n) =
  do len <- localLength
     when (n >= len) $
       traceTCM levelBug $ hsep [text "Context shorter than expected ",
                                 int len, text " <= ", int n]
     b <- localGet n
     w <- whnf (I.lift (n + 1) 0 (bindType b))
     return (Bound n, w)
infer (A.Ident _ x) =   do t <- getGlobal x
                           case t of
                             Definition t1 _ -> do w <- whnf t1
                                                   return (Var x, w)
                             Assumption t1   -> do w <- whnf t1
                                                   return (Var x, w)
                             _               -> __IMPOSSIBLE__
infer xx@(A.Lam _ bs t) =   do (ctx, _) <- inferBinds bs
                               (t', u) <- pushCtx ctx $ infer t
                               return (mkLam (eraseSize ctx) t', mkPi ctx u)
infer (A.App _ e1 e2) = -- inferApp e1 e2
    do (t1, r1) <- infer e1
       case r1 of
         Pi ctx u2 ->
             do let (ch, ct) = ctxSplit ctx
                t2 <- check e2 (bindType ch)
                w  <- whnf $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u2)
                return (mkApp t1 [t2], w)
         _            -> throwNotFunction r1
infer (A.Ind _ an x) =
    do t <- getGlobal x
       i <- fresh
       -- when (an == Star) $ addStarStage i
       case t of
         Inductive k pars pols indices sort _ ->
           return (Ind (Size (Svar i)) x, mkPi (pars +: indices) (Sort sort))
         _                             -> __IMPOSSIBLE__
infer (A.Constr _ x _ pars args) = do
  t <- getGlobal x
  stage <- fresh
  let replStage x = if x == Star then (Size (Svar stage)) else x
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      e <- ask
      traceTCM 20 $ hsep [text "checking ",
                          prettyPrintTCM args,
                          text " againsts ",
                          text (show (foldr subst (replFunc targs) pars')), -- TODO: Add PrettyPrint of Context
                          text "\n env: ", text (show e)] -- TODO: fix (show e). Add PrettyPrint of TCEnv
      args' <- checkList args (foldr subst (replFunc targs) pars')
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = Size (Hat (Svar stage))
          genType = mkApp (Ind indStage indName) (map Bound (reverse [numArgs..numArgs+numPars-1]) ++ indices)
          resType = substList (numArgs + numPars - 1) (pars'++args') genType
          -- foldl (flip (uncurry substN)) genType (zip (reverse [0..numArgs + numPars - 1]) (pars' ++ args'))
      -- We erase the type annotations of both parameters and arguments
      return (Constr (replFunc tpars +: replFunc targs |> (mkBind (Id"") (Ind indStage indName)) ) x (indName, idConstr) (eraseSize pars') (eraseSize args'),
              resType)

    _  -> __IMPOSSIBLE__

infer (A.Fix f) = inferFix f
infer (A.Case c) = inferCase c
infer (A.Number _ _) = __IMPOSSIBLE__ -- Number n is transformed into S (S... O)) during scope checking

-- | Only inductive definitions return more than one global
inferDecl :: (MonadTCM tcm) =>  A.Declaration -> tcm [(Name, Global)]
inferDecl (A.Definition _ x (Just e1) e2) =
    do (t1, r1) <- infer e1
       _ <- isSort r1
       t2 <- check e2 t1
       return [(x, Definition t1 t2)] -- (flatten t1) (flatten t2))]
inferDecl (A.Definition _ x Nothing e) =
    do (t, u) <- infer e
       return [(x, Definition u t)] -- (flatten u) (flatten t))]
inferDecl (A.Assumption _ x e) =
    do (t, r) <- infer e
       _ <- isSort r
       return [(x, Assumption t)] -- (flatten t))]
inferDecl (A.Inductive _ indDef) = inferInd indDef
inferDecl (A.Eval e) =
    do (e1, t1) <- infer e
       r <- reify e1
       liftIO $ putStrLn $ concat ["eval ", show (prettyPrint r), "."]
       e1' <- normalForm e1
       -- traceTCM_ ["Normal form obtained ", show e1']
       r' <- reify e1'
       liftIO $ putStrLn $ show (prettyPrint r')
       return []
inferDecl (A.Check e1 (Just e2)) =
    do (t2, r2) <- infer e2
       _ <- isSort r2
       t1 <- check e1 t2
       t2' <- reify t2
       t1' <- reify t1
       liftIO $ putStrLn $ concat ["check ", PP.renderStyle (PP.style { PP.lineLength=20 }) (prettyPrint t1')]
       liftIO $ putStrLn $ concat ["  : ", PP.renderStyle (PP.style { PP.lineLength=20 }) (prettyPrint t2')]
       return []
inferDecl (A.Check e1 Nothing) =
    do (t1, u1) <- infer e1
       -- traceTCM_ ["checking ", show e1, "\ngiving ", show t1, "\n of type ", show u1]
       u1' <- reify u1
       t1' <- reify t1
       liftIO $ putStrLn $ concat ["check ", show (prettyPrint t1')]
       liftIO $ putStrLn $ concat ["  : ", show (prettyPrint u1')]
       return []




check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term
check t u =   do traceTCM 30 $ (hsep [text "Checking type of", prettyPrintTCM t]
                                <+> hsep [text "against", prettyPrintTCM u])
                 (t', r) <- infer t
                 traceTCM 30 $ hsep [text "Calling subtype with ", prettyPrintTCM r,
                                     text "≤", prettyPrintTCM u]
                 b <- r `subTypeSort` u
                 r__ <- normalForm r >>= reify
                 u__ <- normalForm u >>= reify
                 -- e <- ask
                 -- unless b $ traceTCM_ ["\nCHECK TYPE CONVERSION\n",
                 --                       -- show r, " -> ",
                 --                       show $ prettyPrint r__,
                 --                       "\n==\n",
                 --                       --show u, " -> ",
                 --                       show $ prettyPrint u__, "\n\nin context : ", show e, "\n********\non ", show $ prettyPrint $ getRange t]
                 unless b $ throwNotConvertible r u
                 return t'


checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]
checkList [] EmptyCtx = return []
checkList (e:es) (ExtendCtx b c) = do t <- check e (bindType b)
                                      ts <- checkList es (subst t c)
                                      return (t:ts)
checkList _ _ = __IMPOSSIBLE__
