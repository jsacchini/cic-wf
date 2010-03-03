{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, CPP
  #-}

module Kernel.TypeChecking where

-- import qualified "mtl" Control.Monad.Error as EE
import qualified Control.Exception as E
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Error

import Environment
import Syntax.Bind
import Syntax.Internal hiding (lift)
import qualified Syntax.Internal as I
import qualified Syntax.Abstract as A
import Syntax.Global
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf


checkSort :: (MonadTCM tcm) => A.Sort -> tcm (Term, Type)
checkSort A.Star = return (star, box)
checkSort A.Box = return (box, box)

isSort :: (MonadTCM tcm) => Term -> tcm Sort
isSort (TSort s) = return s
isSort t = do xs <- ask
              typeError $ NotSort xs t

checkProd :: (MonadTCM tcm) => Sort -> Sort -> tcm Sort
checkProd s1 Box = return Box
checkProd s1 Star = return Star
-- checkProd s1 s2 = typeError $ InvalidProductRule s1 s2

-- We assume that in the global environment, types are normalized

infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort r
                         t' <- check t u'
                         w <- whnf u'
                         return (t', w)
infer (A.TSort _ s) = checkSort s
infer (A.Pi _ t1 t2) = do (t1', r1) <- infer (expr t1)
                          s1 <- isSort r1
                          (t2', r2) <- local (fmap (const t1') t1:) $ infer t2
                          s2 <- isSort r2
                          s3 <- checkProd s1 s2
                          return (Pi (fmap (const t1') t1) t2', TSort s3)
infer (A.Bound _ n) = do l <- ask
                         w <- whnf $  I.lift (n+1) 0 $ expr (l !! n)
                         return (Bound n, w)
infer (A.Var _ x) = do t <- lookupGlobal x
                       case t of
                         Def t _ -> do w <- whnf t
                                       return (Free x, w)
                         Axiom t -> do w <- whnf t
                                       return (Free x, w)
infer (A.Lam _ t u) = do (t', r1) <- infer (expr t)
                         s1 <- isSort r1
                         (u', r2) <- local (fmap (const t') t:) $ infer u
                         -- s <- infer g l (Pi t r2)
                         -- isSort s
                         return (Lam (fmap (const t') t) u', Pi (fmap (const t') t) r2)
infer (A.App _ t1 t2) = do (t1', r1) <- infer t1
                           case r1 of
                             Pi b1 u2 -> do t2' <- check t2 (expr b1)
                                            return (App t1' t2', subst t2' u2)
                             otherwise -> throwNotFunction r1

check :: (MonadTCM tcm) => A.Expr -> Term -> tcm Term
check t u = do (t', r) <- infer t
               b <- conversion r u
               unless b $ throwNotConvertible r u
               return t'
