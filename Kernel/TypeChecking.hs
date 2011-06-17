{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
    FlexibleInstances, TypeSynonymInstances
  #-}

module Kernel.TypeChecking where

#include "../undefined.h"
import Utils.Impossible

import Control.Monad.Reader

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
import Utils.Fresh
import Utils.Pretty

checkSort :: (MonadTCM tcm) => Sort -> tcm (Term, Type)
checkSort Prop     = return (Sort Prop, Sort (Type 0))
checkSort (Type n) = return (Sort (Type n), Sort (Type (n + 1)))

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
                                return (ctx1 +: ctx2, max s1 s2)
          inferBind (A.Bind _ [] _) = return (empCtx, Prop)
          inferBind (A.Bind rg (x:xs) e) = do
            (t1, r1) <- infer e
            s1 <- isSort r1
            (ctx, s2) <- pushBind (Bind x t1) $ inferBind (A.Bind rg xs e)
            return (Bind x t1 <| ctx, max s1 s2)
              where mkCtx [] _ _ = empCtx
                    mkCtx (y:ys) t k = Bind y (I.lift k 0 t) <| mkCtx ys t (k + 1)


infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort r
                         t' <- check t u'
                         w <- whnf u'
                         return (t', w)
infer (A.Sort _ s) = checkSort s
infer (A.Pi _ ctx t) =
  do (ctx', s1) <- inferBinds ctx
     (t', r2) <- pushCtx ctx' $ infer t
     s2 <- pushCtx ctx' $ isSort r2
     return (mkPi ctx' t', Sort $ max s1 s2)
infer (A.Arrow _ e1 e2) =
  do (t1, r1) <- infer e1
     s1 <- isSort r1
     (t2, r2) <- pushType t1 $ infer e2
     s2 <- pushType t1 $ isSort r2
     return (mkPi (bindNoName t1 <| empCtx) t2, Sort $ max s1 s2)
infer (A.Bound _ _ n) =
  do l <- ask
     when (n >= length l) $ liftIO $ putStrLn $ concat ["Typechecking ", show n, " ", show l]
     case (l !! n) of
         Bind _ t        -> do w <- whnf (I.lift (n + 1) 0 t)
                               return (Bound n, w)
         LocalDef _ _ t2 -> do w <- whnf (I.lift (n + 1) 0 t2)
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
             do let (ch, ct) = (ctxHd ctx, ctxTl ctx)
                t2 <- check e2 (bindType ch)
                w  <- whnf $ mkPi (subst t2 ct) (substN (ctxLen ct) t2 u2)
                return (mkApp t1 [t2], w)
         _            -> throwNotFunction r1
infer (A.Ind _ an x) =
    do t <- getGlobal x
       i <- getFreshStage
       when (an == Star) $ addStarStage i
       case t of
         Inductive pars pols indices sort _ ->
           return (Ind (Size (Svar i)) x, mkPi (pars +: indices) (Sort sort))
         _                             -> __IMPOSSIBLE__
infer (A.Constr _ x _ pars args) = do
  t <- getGlobal x
  stage <- getFreshStage
  let replStage x = if x == Star then (Size (Svar stage)) else x
      replFunc = modifySize replStage
  case t of
    Constructor indName idConstr tpars targs _ indices -> do
      pars' <- checkList pars (replFunc tpars)
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
infer (A.Number _ _) = __IMPOSSIBLE__

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
       liftIO $ putStrLn $ concat ["check ", show (prettyPrint t1')]
       liftIO $ putStrLn $ concat ["  : ", show (prettyPrint t2')]
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
check t u =   do -- traceTCM_ ["Checking type of\n", show t, "\nagainst\n", show u]
                 (t', r) <- infer t
                 b <- r <~ u
                 r__ <- normalForm r >>= reify
                 u__ <- normalForm u >>= reify
                 e <- ask
                 unless b $ traceTCM_ ["\nCHECK TYPE CONVERSION\n",
                                       -- show r, " -> ",
                                       show $ prettyPrint r__,
                                       "\n==\n",
                                       --show u, " -> ",
                                       show $ prettyPrint u__, "\n\nin context : ", show e, "\n********\non ", show $ prettyPrint $ getRange t]
                 unless b $ throwNotConvertible r u
                 return t'


checkList :: (MonadTCM tcm) => [A.Expr] -> Context -> tcm [Term]
checkList [] EmptyCtx = return []
checkList (e:es) (ExtendCtx b c) = do t <- check e (bindType b)
                                      ts <- checkList es (subst t c)
                                      return (t:ts)
checkList _ _ = __IMPOSSIBLE__
