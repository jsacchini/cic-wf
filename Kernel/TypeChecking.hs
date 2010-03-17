{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, FunctionalDependencies,
  MultiParamTypeClasses,
  CPP
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

-- class Infer a b c | a -> b c where
--     infer :: (MonadTCM tcm) => a -> tcm (b, c)
--     check :: (MonadTCM tcm, Conversion c) => a -> c -> tcm b

--     check t u = do (t', r) <- infer t
--                    b <- conversion r u
--                    unless b $ throwNotConvertible (extractTerm r) (extractTerm u)
--                    return t'

infer :: (MonadTCM tcm) => A.Expr -> tcm (Term, Type)
--instance Infer A.Expr Term Type where
infer (A.Ann _ t u) = do (u', r) <- infer u
                         _ <- isSort r
                         t' <- check t u'
                         w <- whnf u'
                         return (t', w)
infer (A.TSort _ s) = checkSort s
infer (A.Pi _ t1 t2) = do (t1', s1) <- inferBind t1
                          (t2', r2) <- local (t1':) $ infer t2
                          s2 <- local (t1':) $ isSort r2
                          s3 <- checkProd s1 s2
                          return (Pi t1' t2', TSort s3)
infer (A.Bound _ n) = do l <- ask
                         when (n >= length l) $ liftIO $ putStrLn $ concat [show n, " ", show (length l)]
                         w <- whnf $  I.lift (n+1) 0 $ expr (l !! n)
                         return (Bound n, w)
infer (A.Var _ x) = do t <- lookupGlobal x
                       case t of
                         Def t _ -> do w <- whnf t
                                       return (Free x, w)
                         Axiom t -> do w <- whnf t
                                       return (Free x, w)
infer (A.Lam _ t u) = do (t', _) <- inferBind t
                         (u', r2) <- local (t':) $ infer u
                         -- s <- infer g l (Pi t r2)
                         -- isSort s
                         return (Lam t' u', Pi t' r2)
infer (A.App _ t1 t2) = do (t1', r1) <- infer t1
                           case r1 of
                             Pi b1 u2 -> do t2' <- check t2 (expr b1)
                                            return (App t1' t2', subst t2' u2)
                             otherwise -> throwNotFunction r1
infer (A.Ind _ x) = do t <- lookupGlobal x
                       case t of
                         IndDef param arg s _ -> return (Free x, foldr Pi (TSort s) (param++arg))
infer (A.Constr _ _ (iname,k) ps as) =
    do t <- lookupGlobal iname
       case t of
         IndDef cParam cIndex s cs -> do -- liftIO $ putStrLn $ "checking parameters " ++ show (iname,k)
                                         -- xs <- ask
                                         let (MkConstr x cArg tIndex) = cs !! k
                                             -- itype = foldr Pi (TSort s) (cParam++cIndex)
                                             -- bi = Bind iname itype
                                             nParam = length cParam
                                             cArg' = cxtSubst_ nParam (Free iname) cArg
                                         -- liftIO $ putStrLn $ concat ["context\n---\n", show xs, "\n-----\nparams ", show ps, "|" , show as, "\nagainst: ", show cParam, "|", show cArg']
                                         tParamArg <- checkList (ps++as) (cParam++cArg')
                                         let (tParam, tArg) = splitAt (length cParam) tParamArg
                                         -- liftIO $ putStrLn $ concat ["checked param ", show tParam, "|", show tArg]
                                         -- liftIO $ putStrLn $ concat ["check (", show xs, ") ", show as, " :!: ", show (map expr cArg'), " ---- ", show (map expr cArg)]
                                         -- tArg <- {-local (bi:) $-} checkList as cArg'
                                         let tIndex' = map (substList_ 0 (reverse $ tParam++tArg)) tIndex
                                         return (Constr x (iname,k) tParam tArg, foldl App (Free iname) (tParam++tIndex'))

check :: (MonadTCM tcm) => A.Expr -> Term -> tcm Term
check t u = do (t', r) <- infer t
               b <- conversion r u
               unless b $ throwNotConvertible r u
               return t'

checkList :: (MonadTCM tcm) => [A.Expr] -> NamedCxt -> tcm [Term]
checkList [] [] = return []
checkList (e:es) (b:bs) = do xs <- ask
                             -- liftIO $ putStrLn $ concat ["*** ", show e, " :: ", show (expr b)]
                             t <- check e (expr b)
                             ts <- checkList es (cxtSubst t bs)
                             return (t:ts)

-- instance Infer A.BindE BindT Sort where
--     infer (NoBind t) = do (t', u) <- infer t
--                           s <- isSort u
--                           return (NoBind t', s)

inferBind :: (MonadTCM tcm) => A.BindE -> tcm (BindT, Sort)
inferBind (NoBind t) = do (t', r) <- infer t
                          s <- isSort r
                          return (NoBind t', s)
inferBind (Bind x t) = do (t', r) <- infer t
                          s <- isSort r
                          return (Bind x t', s)
inferBind (BindDef x t u) = do (t', r) <- infer t
                               s <- isSort r
                               u' <- check u t'
                               return (BindDef x t' u', s)

checkCxt :: (MonadTCM tcm) => [A.BindE] -> tcm NamedCxt
checkCxt [] = return []
checkCxt (b:bs) = do (b', _) <- inferBind b
                     bs' <- local (b':) (checkCxt bs)
                     return (b':bs')
