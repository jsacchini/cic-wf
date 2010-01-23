{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts 
  #-}

module Typing where

import "mtl" Control.Monad.Error hiding (lift)
import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import Environment
import Internal
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

infer :: GEnv -> LEnv -> A.Expr -> Result Term
infer g l (A.Ann _ t u) = let clu = interp u in
	                    do check g l t clu
                               return clu
infer g l (A.TSort _ s) = checkSort s
infer g l (A.Pi _ x t1 t2) = do r1 <- infer g l t1
                                isSort r1
                                r2 <- infer g ((x,r1):l) t2
                                isSort r2
                                checkProd r1 r2
infer g l (A.Bound _ n) = return $ lift (n+1) 0 $ snd $ l !! n
infer g l (A.Free _ x) = case genvGet g x of
                           Def _ t -> return t
                           Axiom t -> return t
infer g l (A.Lam _ x t u) = do r1 <- infer g l t
                               isSort r1
                               r2 <- infer g ((x,interp t):l) u
                               -- s <- infer g l (Pi t r2)
                               -- isSort s
                               return $ Pi x (interp t) r2
infer g l (A.App _ t1 t2) = do r1 <- infer g l t1
                               r2 <- infer g l t2
                               case r1 of
                                   Pi _ u1 u2 -> do conversion g r2 u1
                                                    return $ subst (interp t2) u2
                                   otherwise -> throwError $ NotFunction r2

mapp :: Term -> [Term] -> Term
mapp = foldl App

-- mpi :: Term -> NamedCxt -> Term
-- mpi = foldr $ uncurry $ Pi

if_ :: Monad m => Bool -> m () -> m ()
if_ True t = t
if_ False _ = return ()

check :: GEnv -> LEnv -> A.Expr -> Term -> Result ()
check g l t u = do r <- infer g l t
                   conversion g r u

lcheck :: GEnv -> LEnv -> [A.Expr] -> [Term] -> Result ()
lcheck _ _ [] [] = return ()
lcheck g l (t:ts) (u:us) = do check g l t u
			      lcheck g l ts (mapsubst 0 (interp t) us)
