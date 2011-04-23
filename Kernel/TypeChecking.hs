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
import Control.Monad.Reader
import Control.Monad.Error

import Data.Function

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import Kernel.Inductive

checkSort :: (MonadTCM tcm) => A.Sort -> tcm (Term, Type)
checkSort A.Prop = return (tProp, tType 0)
checkSort (A.Type n) = return (tType n, tType (n + 1))

isSort :: (MonadTCM tcm) => Term -> tcm Sort
isSort (Sort s) = return s
isSort t = do xs <- ask
              typeError $ NotSort xs t

-- We assume that in the global environment, types are normalized

class Infer a b | a -> b where
  infer :: (MonadTCM tcm) => a -> tcm b

class Check a b c | a -> b c where
  check :: (MonadTCM tcm) => a -> b -> tcm c

  -- check t u = do (t', r) <- infer t
  --                b <- conversion r u
  --                unless b $ throwNotConvertible (extractTerm r) (extractTerm u)
  --                return t'

instance Infer A.Bind ([Bind], Sort) where
  infer (A.Bind r xs e) =
    do (t, r) <- infer e
       s <- isSort r
       return (mkBinds xs t 0, s)
         where mkBinds [] _ _ = []
               mkBinds (x:xs) t k = Bind x (I.lift k 0 t) : mkBinds xs t (k + 1)

instance (Infer a ([Bind], Sort)) => Infer [a] ([Bind], Sort) where
  infer []     = return ([], Prop)
  infer (x:xs) = do (bs1, s1) <- infer x
                    (bs2, s2) <- local (reverse bs1++) $ infer xs
                    return (bs1 ++ bs2, max s1 s2)

instance Infer A.Expr (Term, Type) where
--instance Infer A.Expr Term Type where
  infer (A.Ann _ t u) = do (u', r) <- infer u
                           _ <- isSort r
                           t' <- check t u'
                           w <- whnf u'
                           return (t', w)
  infer (A.Sort _ s) = checkSort s
  infer (A.Pi _ bs t) =
    do (bs', s1) <- infer bs
       (t', r2) <- local (reverse bs'++) $ infer t
       s2 <- local (reverse bs'++) $ isSort r2
       return (buildPi bs' t', Sort $ max s1 s2)
  infer (A.Arrow _ e1 e2) =
    do (t1, r1) <- infer e1
       s1 <- isSort r1
       (t2, r2) <- local (bindNoName t1:) $ infer e2
       s2 <- local (bindNoName t1:) $ isSort r2
       return (buildPi [bindNoName t1] t2, Sort $ max s1 s2)
  infer (A.Bound _ x n) =
    do l <- ask
       when (n >= length l) $ liftIO $ putStrLn $ concat ["Typechecking ", show n, " ", show l]
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
  infer (A.Lam _ bs t) = do (bs', _) <- infer bs
                            (t', u) <- local (reverse bs'++) $ infer t
                            return (buildLam bs' t', buildPi bs' u)
  infer (A.App _ e1 e2) = -- inferApp e1 e2
    do (t1, r1) <- infer e1
       case r1 of
         Pi (b:bs) u2 -> do t2 <- check e2 (bindType b)
                            w   <- whnf $ buildPi (subst t2 bs) (substN (length bs) t2 u2)
                            return (buildApp t1 [t2], w)
         otherwise    -> throwNotFunction r1
  infer (A.Ind _ x) =
    do t <- getGlobal x
       case t of
         Inductive pars indices sort _ ->
           return (Ind x, buildPi (pars ++ indices) (Sort sort))
         _                             -> __IMPOSSIBLE__
  infer (A.Constr r x _ pars args) =
    do t <- getGlobal x
       case t of
         Constructor indName id tpars targs indices ->
           do pars' <- check pars tpars
              args' <- check args (foldr subst targs pars')
              return (Constr x (indName, id) pars' args',
                      buildApp (Ind indName) (pars' ++ foldr subst indices (pars' ++ args')))
  infer e = do liftIO $ putStrLn $ "\n\n----> " ++ show e
               error "typechecking: not implemented"



-- inferBind :: (MonadTCM tcm) => A.Bind -> tcm ([Bind], Sort)
-- inferBind (A.Bind r xs e) =
--   do (t, r) <- infer e
--      s <- isSort r
--      return (mkBinds xs t 0, s)
--        where mkBinds [] _ _ = []
--              mkBinds (x:xs) t k = Bind x (I.lift k 0 t) : mkBinds xs t (k + 1)

-- inferBinds :: (MonadTCM tcm) => [A.Bind] -> tcm ([Bind], Sort)
-- inferBinds [] = return ([], Prop)
-- inferBinds (b:bs) = do -- liftIO $ putStrLn $ "inferBinds "  ++ show (b:bs)
--                        (bs1, s1) <- inferBind b
--                        (bss1, s2) <- local (reverse bs1++) $ inferBinds bs
--                        return (bs1 ++ bss1, max s1 s2)


-- | Only inductive definitions return more than one global
instance Infer A.Declaration [(Name, Global)] where
  infer (A.Definition _ x (Just e1) e2) =
    do (t1, r1) <- infer e1
       _ <- isSort r1
       t2 <- check e2 t1
       return [(x, Definition (flatten t2) (flatten t1))]
  infer (A.Definition _ x Nothing e) =
    do (t, u) <- infer e
       return [(x, Definition (flatten u) (flatten t))]
  infer (A.Assumption _ x e) =
    do (t, r) <- infer e
       _ <- isSort r
       return [(x, Assumption (flatten t))]
  infer (A.Inductive _ indDef) = infer indDef

instance Check A.Expr Type Term where
  check t u = do (t', r) <- infer t
                 b <- conversion r u
                 unless b $ liftIO $ putStrLn $ show r ++ "\n==\n" ++ show u
                 unless b $ throwNotConvertible r u
                 return t'


instance Check [A.Expr] [Bind] [Term] where
  check [] [] = return []
  check (e:es) (b:bs) = do t <- check e (bindType b)
                           ts <- check es (subst t bs)
                           return (t:ts)