{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts 
  #-}

module Typing where

import "mtl" Control.Monad.Error hiding (lift)
import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Environment
import Internal hiding (lift)
import qualified Internal as I
import qualified Abstract as A
import Parser
import Conversion
import TCM


checkSort :: A.Sort -> Result Term
checkSort A.Star = return (TSort Box)
checkSort A.Box = return (TSort Box)

isSort :: Term -> Result ()
isSort (TSort _) = return ()
isSort t = throwError $ NotSort t

checkProd :: Term -> Term -> Result Term
checkProd (TSort s1) (TSort Box) = return $ TSort Box
checkProd (TSort s1) (TSort Star) = return $ TSort Star
checkProd t1 t2 = throwError $ InvalidProductRule t1 t2

-- We assume that in the global environment, types are normalized

infer :: A.Expr -> Result Term
infer (A.Ann _ t u) = let clu = interp u in
                        do check t clu
                           return clu
infer (A.TSort _ s) = checkSort s
infer (A.Pi _ x t1 t2) = do r1 <- infer t1
                            isSort r1
                            r2 <- local (interp t1:) $ infer t2
                            isSort r2
                            checkProd r1 r2
infer (A.Bound _ n) = do l <- ask
                         return $ I.lift (n+1) 0 $ l !! n
infer (A.Free _ x) = do t <- lookupGlobal x 
                        case t of
                          Def _ t -> return t
                          Axiom t -> return t
infer (A.Lam _ x t u) = do r1 <- infer t
                           isSort r1
                           r2 <- local (interp t:) $ infer u
                           -- s <- infer g l (Pi t r2)
                           -- isSort s
                           return $ Pi x (interp t) r2
infer (A.App _ t1 t2) = do r1 <- infer t1
                           r2 <- infer t2
                           case r1 of
                             Pi _ u1 u2 -> do conversion r2 u1
                                              return $ subst (interp t2) u2
                             otherwise -> throwError $ NotFunction r2

mapp :: Term -> [Term] -> Term
mapp = foldl App

-- mpi :: Term -> NamedCxt -> Term
-- mpi = foldr $ uncurry $ Pi

if_ :: Monad m => Bool -> m () -> m ()
if_ True t = t
if_ False _ = return ()

check :: A.Expr -> Term -> Result ()
check t u = do r <- infer t
               conversion r u

lcheck :: [A.Expr] -> [Term] -> Result ()
lcheck [] [] = return ()
lcheck (t:ts) (u:us) = do check t u
	                  lcheck ts (mapsubst 0 (interp t) us)
