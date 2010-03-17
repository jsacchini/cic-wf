{-# LANGUAGE PackageImports #-}
module Kernel.Inductive (processInd) where

-- import Prelude hiding (catch)

import "mtl" Control.Monad.Reader
import qualified Control.Exception as E

import qualified Syntax.Abstract as A
import Syntax.Bind
import Syntax.Name
import Syntax.Internal
import Syntax.Global

import Kernel.GlobalMonad hiding (infer, isSort)
import Kernel.TCM
import Kernel.TypeChecking
import Kernel.Whnf

{---
TODO:
 - positivity check in constructors
---}

processInd :: (TCGlobalMonad gm) => A.IndExpr -> gm ()
processInd i = do i'@(IndDef params args sort cs) <- flip runReaderT [] $ checkInd i
                  checkIfDefined (iName:map constrName cs)
                  extendName iName i'
                  foldM (addConstr params args sort) 0 cs
                  return ()
    where indName (A.MkInd x _ _ _) = x
          iName = indName i
          constrName (MkConstr x _ _) = x
          addConstr p a s k (MkConstr x as us) = do extendName x (ConstrDef (iName,k) p a s as us)
                                                    return (k+1)

checkInd :: (MonadTCM tcm) => A.IndExpr -> tcm Global
checkInd (A.MkInd x params arg cs) = do params' <- checkCxt params
                                        (arg', _) <- infer arg
                                        xs <- ask
                                        (args, sort) <- checkArity (xs, arg') arg'
                                        let paramNum = length params
                                            indParam = reverse $ makeInd params' args sort:params'
                                        cs' <- mapM (local (indParam++) . checkConstr (paramNum, paramNum)) cs
                                        return $ IndDef params' args sort cs'
    where makePi cxt t = foldr Pi t cxt
          makeInd p a s = Bind x (makePi (p++a) (TSort s))

checkArity :: (MonadTCM tcm) => (TCEnv, Term) -> Term -> tcm (NamedCxt, Sort)
checkArity e t = do w <- whnf t
                    case w of
                      Pi u1 u2 -> do (cxt, s) <- local (u1:) (checkArity e u2)
                                     return (u1:cxt, s)
                      TSort s -> return ([], s)
                      _ -> typeError $ uncurry NotArity e

checkConstr :: (MonadTCM tcm) => (Int, Int) -> A.ConstrExpr -> tcm Constr
checkConstr i (A.MkConstrExpr x e) = do liftIO $ putStrLn $ "infer " ++ x
                                        (t, r) <- infer e
                                        isSort r
                                        xs <- ask
                                        (args, us) <- positive i t -- checkConstrType (xs, t) t
                                        return $ MkConstr x args us
    where checkConstrType e t = do w <- whnf t
                                   case w of
                                     Pi u1 u2 -> do (args, us) <- checkConstrType e u2
                                                    return (u1:args, us)
                                     Bound n -> return ([], []) -- complete
                                     _ -> typeError $ uncurry NotConstructor e
          positive i@(iname,paramNum) t = do w <- whnf t
                                             case w of
                                               Pi u1 u2 -> do strictPos i (expr u1)
                                                              (args, us) <- positive (iname+1,paramNum) u2
                                                              return (u1:args,us)
                                               u -> do us <- getIndices i u
                                                       return ([], us)
          strictPos i@(iname,paramNum) t | not (isFree iname t) = return ()
                                         | otherwise =
                                           do w <- whnf t
                                              case w of
                                                Pi u1 u2 -> do when (isFree iname (expr u1)) $ typeError $ ConstantError "not strictly positive"
                                                               strictPos (iname+1,paramNum) u2
                                                u-> do _ <- getIndices i u
                                                       return ()
          getIndices i@(iname,paramNum) t = do (f,args) <- getArgs t
                                               wellApplied iname paramNum f args
                                               -- return [] -- complete
          wellApplied iname paramNum (Bound k) args = do liftIO $ putStrLn $ concat [show paramNum, " ", show (iname-1), " ** ", show args, " ", show k]
                                                         when (k /= iname) $ typeError $ ConstantError "algo"
                                                         checkArgs paramNum (iname-1) args
          wellApplied _ _ _ _ = typeError $ ConstantError "algo 2"
          checkArgs 0 k us = return us
          checkArgs (p+1) k (Bound u:us) = do liftIO $ putStrLn $ concat [show (p+1), " ", show k, " = ", show (Bound u:us)]
                                              when (u /= k) $ typeError $ ConstantError "algo 3"
                                              checkArgs p (k-1) us
          checkArgs a b c = do liftIO $ putStrLn $ concat [show a, " ", show b, " - ", show c]
                               typeError $ ConstantError "algo 4"
          getArgs t = do w <- whnf t
                         case w of
                           App u1 u2 -> do (f,args) <- getArgs u1
                                           return (f,args++[u2])
                           u@(Bound n) -> return (u,[])
                           _ -> typeError $ ConstantError "inductive not applied"
