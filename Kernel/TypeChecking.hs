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

import Data.Functor
import Data.Maybe

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
import Kernel.TCMErrors
import Kernel.Whnf
import Kernel.Inductive (inferInd)
import Kernel.Fix (inferFix)
import Kernel.Case (inferCase)
import Kernel.PrettyTCM
import Utils.Fresh
import qualified Utils.Pretty as MP


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
isSort t = do t' <- whnF t
              case t' of
                Sort s -> return s
                _      -> do xs <- ask
                             typeError $ NotSort xs t

-- We assume that in the global environment, types are normalized

inferBinds :: (MonadTCM tcm) => A.Context -> tcm (Context, Sort)
inferBinds CtxEmpty = return (CtxEmpty, Prop)
inferBinds (CtxExtend b bs) = do (ctx1, s1) <- inferBind b
                                 (ctx2, s2) <- pushCtx ctx1 $ inferBinds bs
                                 s' <- maxSort s1 s2
                                 return (ctx1 +: ctx2, s')
  where
    inferBind (A.Bind _ [] _) = __IMPOSSIBLE__
    inferBind (A.Bind _ (x:xs) e) = do
      (t1, r1) <- infer (fromJust (implicitValue e))
      s1 <- isSort r1
      return (ctxFromList (mkCtx (x:xs) t1 0), s1)
        where
          impl = isImplicit e
          mkCtx [] _ _ = []
          mkCtx (y:ys) t k = mkImplBind y impl (I.lift k 0 t) : mkCtx ys t (k + 1)


infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort r
                         t' <- check t u'
                         w <- whnF u'
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
infer exp@(A.Arrow _ e1 e2) = -- TODO: check arrows with implicit arguments
  do traceTCM 30 $ hsep [text "Inferring arrow",
                         prettyPrintTCM exp]
     (t1, r1) <- infer (implicitValue e1)
     s1 <- isSort r1
     (t2, r2) <- pushType t1 $ infer e2
     s2 <- pushType t1 $ isSort r2
     s' <- checkProd s1 s2
     return (mkPi (ctxSingle (unNamed t1)) t2, Sort s')
infer (A.Bound _ _ n) =
  do len <- localLength
     traceTCM 30 $ vcat [ text "infer Bound" <+> prettyPrintTCM n
                        , text "in ctx   " <+> (ask >>= prettyPrintTCM) ]
     when (n >= len) $
       traceTCM levelBug $ hsep [text "Context shorter than expected ",
                                 int len, text " <= ", int n]
     b <- localGet n
     w <- whnF (I.lift (n + 1) 0 (bindType b))
     return (Bound n, w)
infer (A.Ident _ x) =   do t <- getGlobal x
                           case t of
                             Definition {} -> return (Var x, defType t)
                             Assumption {} -> return (Var x, assumeType t)
                             _             -> __IMPOSSIBLE__
infer xx@(A.Lam _ bs t) =   do (ctx, _) <- inferBinds bs
                               (t', u) <- pushCtx ctx $ infer t
                               return (mkLam (eraseSize ctx) t', mkPi ctx u)
infer (A.App _ e1 e2) = -- inferApp e1 e2
    do (t1, r1) <- infer e1
       traceTCM 30 $ vcat [ text "Checking function part"
                          , text "from" <+> prettyPrintTCM e1
                          , text "to" <+> prettyPrintTCM t1
                          , text "of type" <+> prettyPrintTCM r1]
       case r1 of
         Pi ctx u2 ->
             do let (ch, ct) = ctxSplit ctx
                t2 <- check e2 (bindType ch)
                w  <- whnF $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u2)
                traceTCM 30 $ hsep [ text "Checked APP:"
                                   , prettyPrintTCM (mkApp t1 [t2]) ]
                traceTCM 30 $ hsep [ text "APP result type:"
                                   , prettyPrintTCM w ]
                return (mkApp t1 [t2], w)
         _            -> throwNotFunction r1
infer (A.Meta r _) = typeError $ CannotInferMeta r
infer (A.Ind _ an x _) =
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
  let -- Star signals recursive occurrences of the inductive type. See Kernel.Inductive
      replStage x = if x == Star then (Size (Svar stage)) else x
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
      traceTCM 20 $ (hsep [text "checking constructor args",
                           prettyPrintTCM args,
                           text " againsts ",
                           prettyPrintTCM $ mkPi (foldr subst (replFunc targs) pars') (Sort Prop)
                           ]
                     $$ hsep [text "env:", ask >>= prettyPrintTCM])
      args' <- checkList args (foldr subst (replFunc targs) pars')
      let numPars = ctxLen tpars
          numArgs = ctxLen targs
          indStage = Size (Hat (Svar stage))
          genType = mkApp (Ind indStage indName) (map Bound (reverse [numArgs..numArgs+numPars-1]) ++ indices)
          resType = substList (numArgs + numPars - 1) (pars'++args') genType
          -- foldl (flip (uncurry substN)) genType (zip (reverse [0..numArgs + numPars - 1]) (pars' ++ args'))
      -- We erase the type annotations of both parameters and arguments
      return (Constr x (indName, idConstr) (eraseSize pars') (eraseSize args'),
              resType)

    _  -> __IMPOSSIBLE__

infer (A.Fix f) = inferFix f
infer (A.Case c) = inferCase c
infer (A.Number _ _) = __IMPOSSIBLE__ -- Number n is transformed into S (S... O)) during scope checking

-- | Only inductive definitions return more than one global
inferDecl :: (MonadTCM tcm) =>  A.Declaration -> tcm [(Named Global)]
inferDecl (A.Definition _ x (Just e1) e2) =
    do (tp, s) <- infer e1
       _ <- isSort s
       def <- check e2 tp
       return [mkNamed x (Definition { defType = tp
                                     , defTerm = def })]
inferDecl (A.Definition _ x Nothing e) =
    do (def, tp) <- infer e
       return [mkNamed x (Definition { defType = tp
                                     , defTerm = def })] -- (flatten u) (flatten t))]
inferDecl (A.Assumption _ x e) =
    do (t, r) <- infer e
       _ <- isSort r
       return [mkNamed x (Assumption t)] -- (flatten t))]
inferDecl (A.Inductive _ indDef) = inferInd indDef
inferDecl (A.Eval e) =
    do (e1, t1) <- infer e
       r <- reify e1
       traceTCM 70 $ hsep [text "eval ", prettyPrintTCM e1 <> dot]
       e1' <- nF e1
       traceTCM 70 $ vcat [text "Normal form obtained ", text (show e1')]
       traceTCM 70 $ vcat [text "Normal form obtained ", prettyPrintTCM e1']
       printTCMLn $ prettyPrintTCM e1'
       return []
inferDecl (A.Check e1 (Just e2)) =
    do (t2, r2) <- infer e2
       _ <- isSort r2
       t1 <- check e1 t2
       traceTCM 70 $ hsep [text "check ", prettyPrintTCM t1, text " : "]
       printTCMLn $ prettyPrintTCM t2
       return []
inferDecl (A.Check e1 Nothing) =
    do (t1, u1) <- infer e1
       -- traceTCM_ ["checking ", show e1, "\ngiving ", show t1, "\n of type ", show u1]
       traceTCM 70 $ hsep [text "check ", prettyPrintTCM t1, text " : "]
       printTCMLn $ prettyPrintTCM u1
       return []




check :: (MonadTCM tcm) => A.Expr -> Type -> tcm Term
check (A.Meta r Nothing) u = do
  m <- fresh
  e <- ask
  addGoal m (mkGoal e u)
  return (Meta m)
check t u =   do traceTCM 30 $ (hsep [text "Checking type of", prettyPrintTCM t]
                                <+> hsep [text "against", prettyPrintTCM u])
                 (t', r) <- infer t
                 traceTCM 30 $ hsep [text "Calling subtype with ", prettyPrintTCM r,
                                     text "≤", prettyPrintTCM u]
                 b <- r `subTypeSort` u
                 -- r__ <- nF r >>= reify
                 -- u__ <- nF u >>= reify
                 -- e <- ask
                 -- unless b $ traceTCM_ ["\nCHECK TYPE CONVERSION\n",
                 --                       -- show r, " -> ",
                 --                       show $ prettyPrint r__,
                 --                       "\n==\n",
                 --                       --show u, " -> ",
                 --                       show $ prettyPrint u__, "\n\nin context : ", show e, "\n********\non ", show $ prettyPrint $ getRange t]
                 unless b $ throwNotConvertible (Just (range t)) r u
                 return t'


checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]
checkList es CtxEmpty = return []
checkList (e:es) (CtxExtend b bs) =
  do
    t <- check e (bindType b)
    ts <- checkList es (subst t bs)
    return (t:ts)
checkList _ _ = __IMPOSSIBLE__
