{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, FunctionalDependencies,
  MultiParamTypeClasses,
  CPP
  #-}

module Kernel.TypeChecking where

#include "../undefined.h"
import Utils.Impossible

-- import qualified "mtl" Control.Monad.Error as EE
import qualified Control.Exception as E
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Error

import Data.Function

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf


checkSort :: (MonadTCM tcm) => A.Sort -> tcm (Term, Type)
checkSort A.Prop = return (tProp, tType 0)
checkSort (A.Type n) = return (tType n, tType (n + 1))

isSort :: (MonadTCM tcm) => Term -> tcm Sort
isSort (Sort s) = return s
isSort t = do xs <- ask
              typeError $ NotSort xs t

-- We assume that in the global environment, types are normalized

-- class Infer a b c | a -> b c where
--   infer :: (MonadTCM tcm) => a -> tcm (b, c)
--   check :: (MonadTCM tcm, Conversion c) => a -> c -> tcm b

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
infer (A.Sort _ s) = checkSort s
infer (A.Pi _ bs t) = do (bs', s1) <- inferBinds bs
                         (t', r2) <- local (reverse bs'++) $ infer t
                         s2 <- local (reverse bs'++) $ isSort r2
                         return (Pi bs' t', Sort $ max s1 s2)
infer (A.Bound _ x n) =
  do l <- ask
     when (n >= length l) $ liftIO $ putStrLn $ concat [show n, " ", show (length l)]
     case (l !! n) of
       Bind x t -> do w <- whnf (I.lift (n + 1) 0 t)
                      return (Bound n, w)
       LocalDef x t1 t2 -> do w <- whnf (I.lift (n + 1) 0 t2)
                              return (Bound n, w)
infer (A.Var _ x) = do t <- getGlobal x
                       case t of
                         Definition t _ -> do w <- whnf t
                                              return (Var x, w)
                         Assumption t   -> do w <- whnf t
                                              return (Var x, w)
                         _              -> __IMPOSSIBLE__
infer (A.Lam _ bs t) = do (bs', _) <- inferBinds bs
                          (t', u) <- local (reverse bs'++) $ infer t
                          return (Lam bs' t', Pi bs' u)
-- infer (A.App _ t1 t2) = do (t1', r1) <- infer t1
--                            case r1 of
--                              Pi b1 u2 -> do t2' <- check t2 (expr b1)
--                                             return (App t1' t2', subst t2' u2)
--                              otherwise -> throwNotFunction r1



inferBind :: (MonadTCM tcm) => A.Bind -> tcm ([Bind], Sort)
inferBind (A.Bind r xs e) =
  do (t, r) <- infer e
     s <- isSort r
     return (mkBinds xs t 0, s)
       where mkBinds [] _ _ = []
             mkBinds (x:xs) t k = Bind x (I.lift k 0 t) : mkBinds xs t (k + 1)
inferBind (A.NoBind e) =
  do (t, r) <- infer e
     s <- isSort r
     return ([NoBind t], s)

inferBinds :: (MonadTCM tcm) => [A.Bind] -> tcm ([Bind], Sort)
inferBinds [] = return ([], Prop)
inferBinds (b:bs) = do -- liftIO $ putStrLn $ "inferBinds "  ++ show (b:bs)
                       (bs1, s1) <- inferBind b
                       (bss1, s2) <- local (reverse bs1++) $ inferBinds bs
                       return (bs1 ++ bss1, max s1 s2)


inferDecl :: (MonadTCM tcm) => A.Declaration -> tcm Global
inferDecl (A.Definition _ x (Just e1) e2) =
  do (t1, r1) <- infer e1
     _ <- isSort r1
     t2 <- check e2 t1
     return $ Definition (flatten t2) (flatten t1)
inferDecl (A.Definition _ x Nothing e) =
  do (t, u) <- infer e
     return $ Definition (flatten u) (flatten t)
inferDecl (A.Assumption _ x e) =
  do (t, r) <- infer e
     _ <- isSort r
     return $ Assumption (flatten t)
inferDecl _ = error "not yet"


-- infer (A.Ind _ x) = do t <- lookupGlobal x
--                        case t of
--                          IndDef param arg s _ -> return (Free x, foldr Pi (TSort s) (param+|+arg))
-- infer (A.Constr _ _ (iname,k) ps as) =
--     do t <- lookupGlobal iname
--        case t of
--          IndDef cParam cIndex s cs -> do -- liftIO $ putStrLn $ "checking parameters " ++ show (iname,k)
--                                          -- xs <- ask
--                                          let (MkConstr x cArg tIndex) = cs !! k
--                                              -- itype = foldr Pi (TSort s) (cParam++cIndex)
--                                              -- bi = Bind iname itype
--                                              nParam = cxtSize cParam
--                                              cArg' = liftCxt (flip subst_ (Free iname)) nParam cArg
--                                          -- liftIO $ putStrLn $ concat ["context\n---\n", show xs, "\n-----\nparams ", show ps, "|" , show as, "\nagainst: ", show cParam, "|", show cArg']
--                                          tParamArg <- checkList (ps++as) (cParam+|+cArg')
--                                          let (tParam, tArg) = splitAt (cxtSize cParam) tParamArg
--                                          -- liftIO $ putStrLn $ concat ["checked param ", show tParam, "|", show tArg]
--                                          -- liftIO $ putStrLn $ concat ["check (", show xs, ") ", show as, " :!: ", show (map expr cArg'), " ---- ", show (map expr cArg)]
--                                          -- tArg <- {-local (bi:) $-} checkList as cArg'
--                                          let tIndex' = map (substList_ 0 (reverse $ tParam++tArg)) tIndex
--                                          return (Constr x (iname,k) tParam tArg, foldl App (Free iname) (tParam++tIndex'))

check :: (MonadTCM tcm) => A.Expr -> Term -> tcm Term
check t u = do (t', r) <- infer t
               b <- conversion r u
               unless b $ throwNotConvertible r u
               return t'

-- checkList :: (MonadTCM tcm) => [A.Expr] -> NamedCxt -> tcm [Term]
-- checkList [] [] = return []
-- checkList (e:es) (b:bs) = do xs <- ask
--                              -- liftIO $ putStrLn $ concat ["*** ", show e, " :: ", show (expr b)]
--                              t <- check e (expr b)
--                              ts <- checkList es (liftCxt (flip subst_ t) 0 bs)
--                              return (t:ts)

-- -- instance Infer A.BindE BindT Sort where
-- --     infer (NoBind t) = do (t', u) <- infer t
-- --                           s <- isSort u
-- --                           return (NoBind t', s)

-- inferBind :: (MonadTCM tcm) => A.BindE -> tcm (BindT, Sort)
-- inferBind (NoBind t) = do (t', r) <- infer t
--                           s <- isSort r
--                           return (NoBind t', s)
-- inferBind (Bind x t) = do (t', r) <- infer t
--                           s <- isSort r
--                           return (Bind x t', s)
-- inferBind (BindDef x t u) = do (t', r) <- infer t
--                                s <- isSort r
--                                u' <- check u t'
--                                return (BindDef x t' u', s)

-- checkCxt :: (MonadTCM tcm) => [A.BindE] -> tcm NamedCxt
-- checkCxt [] = return []
-- checkCxt (b:bs) = do (b', _) <- inferBind b
--                      bs' <- local (b':) (checkCxt bs)
--                      return (b':bs')
