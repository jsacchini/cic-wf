{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}

{-|
  TODO

  - Generation of fresh names is slow (not that it matters). See freshName

  - Bound variables that do not appear in the body must be dealt with:

    * for products, replace forall by "->"

    * for functions, replace name by "_"
-}

module Syntax.InternaltoAbstract where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Set as Set
import Data.Set (Set)

import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Kernel.TCM
import Syntax.Position
import Syntax.Common
import Syntax.Scope (fakeBinds)
import Utils.Misc

class Reify a b | a -> b where
  reify :: (MonadTCM tcm) => a -> tcm b

instance Reify Sort A.Sort where
  reify Prop = return A.Prop
  reify (Type n) = return $ A.Type n

freshName :: [Name] -> Name -> Name
freshName xs y | y `notElem` xs = y
               | otherwise = trySuffix 0
                 where trySuffix n | addSuffix y n `notElem` xs = addSuffix y n
                                   | otherwise = trySuffix (n+1)
                       addSuffix (Id x) n = Id $ x ++ show n

pickFreshName :: (MonadTCM tcm) => Name -> tcm Name
pickFreshName x | isNull x  = return $ Id "_"
                | otherwise = do xs <- getLocalNames
                                 return $ freshName xs x

pickFreshNames :: (MonadTCM tcm) => [Name] -> tcm [Name]
pickFreshNames []     = return []
pickFreshNames (x:xs) = do x' <- pickFreshName x
                           xs' <- fakeBinds x' $ pickFreshNames xs
                           return $ x' : xs'


reifyPiBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm A.Expr
reifyPiBinds = rP []
  where
    rP :: (MonadTCM tcm) => [A.Bind] -> [Bind] -> Term -> tcm A.Expr
    rP [] [] t                  = reify t
    rP bs [] t                  = do e <- reify t
                                     return $ A.Pi noRange (reverse bs) e
    rP [] bs@(Bind x t1:bs') t2
      | notFree bs' t2 =
        do liftIO $ putStrLn $ "notFree 1 " ++ show bs ++ " -> " ++ show t2
           e1 <- reify t1
           e2 <- fakeBinds noName $ rP [] bs' t2
           return $ A.Arrow noRange e1 e2
      | otherwise     =
          do liftIO $ putStrLn $ "otherwise 1 " ++ show bs ++ " -> " ++ show t2
             e1 <- reify t1
             x' <- pickFreshName x
             fakeBinds x' $ rP [A.Bind noRange [x'] e1] bs' t2
    rP bs1@(A.Bind _ xs e1:bs1') bs2@(Bind y t1:bs2') t2
      | notFree bs2' t2 =
        do e2 <- rP [] bs2 t2
           return $ A.Pi noRange (reverse bs1) e2
      | otherwise     =
          do e1' <- reify t1
             y' <- pickFreshName y
             if e1 == e1'
               then fakeBinds y' $ rP (A.Bind noRange (xs++[y']) e1:bs1') bs2' t2
               else fakeBinds y' $ rP (A.Bind noRange [y'] e1':bs1) bs2' t2
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])

reifyLamBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm A.Expr
reifyLamBinds = rL []
  where
    rL :: (MonadTCM tcm) => [A.Bind] -> [Bind] -> Term -> tcm A.Expr
    rL bs [] t                  = do e <- reify t
                                     return $ A.Lam noRange (reverse bs) e
    rL [] bs@(Bind x t1:bs') t2 =
      do e1 <- reify t1
         x' <- if notFree bs' t2 then return (Id "_") else pickFreshName x
         fakeBinds x' $ rL [A.Bind noRange [x'] e1] bs' t2
    rL bs1@(A.Bind _ xs e1:bs1') bs2@(Bind y t1:bs2') t2 =
      do e1' <- reify t1
         y' <- if notFree bs2' t2 then return (Id "_") else pickFreshName y
         if e1 == e1'
           then fakeBinds y' $ rL (A.Bind noRange (xs++[y']) e1:bs1') bs2' t2
           else fakeBinds y' $ rL (A.Bind noRange [y'] e1':bs1) bs2' t2
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])


instance Reify Term A.Expr where
  reify (Sort s) = do s' <- reify s
                      return $ A.Sort noRange s'
  reify (Pi bs t) = do liftIO $ putStrLn $ "printing " ++ show (Pi bs t)
                       liftIO $ putStrLn $ "reifyBinds " ++ show bs
                       reifyPiBinds bs t
  reify (Bound n) = do xs <- getLocalNames
                       l <- ask
                       when (n >= length xs) $ get >>= \st -> liftIO $ putStrLn $ "InternaltoAbstract Bound " ++ " " ++ show n ++ "  -- " ++ show l ++ " \n\n" ++ show st
                       return $ A.Var noRange (xs !! n)
  reify (Var x) = return $ A.Var noRange x
  reify (Lam bs t) = reifyLamBinds bs t
  reify (App t ts) = do e <- reify t
                        es <- mapM reify ts
                        return $ mkApp e es
                          where mkApp = foldl (A.App noRange)
  reify (Ind i) = return $ A.Ind noRange i
  reify (Constr x indId ps as) =
    do ps' <- mapM reify ps
       as' <- mapM reify as
       return $ A.Constr noRange x indId ps' as'

instance Reify Name A.Declaration where
  reify x =
    do g <- getGlobal x
       case g of
         I.Definition t1 t2 -> do e1 <- reify t1
                                  e2 <- reify t2
                                  return $ A.Definition noRange x (Just e1) e2
         I.Assumption t -> do e <- reify t
                              return $ A.Assumption noRange x e
         t@(I.Inductive pars indices sort constr) ->
           do liftIO $ putStrLn $ "data " ++ show x ++ " : " ++ show t
              return $ A.Inductive noRange (A.InductiveDef x [] (A.Sort noRange A.Prop) [])
           -- COMPLETE THIS CASE
         t@(Constructor _ _ _ _ _) ->
           do liftIO $ putStrLn $ "constructor " ++ show x ++ " : " ++ show t
              return $ A.Assumption noRange x (A.Sort noRange A.Prop)


-- | Free bound variables

class IsFree a where
  isFree :: Int -> a -> Bool

instance IsFree Term where
  isFree k (Sort _) = False
  isFree k (Pi [] t) = isFree k t
  isFree k (Pi (b:bs) t) = isFree k b || isFree (k+1) (Pi bs t)
  isFree k (Bound n) = k == n
  isFree k (Var _) = False
  isFree k (Lam [] t) = isFree k t
  isFree k (Lam (b:bs) t) = isFree k b || isFree (k+1) (Lam bs t)
  isFree k (App f ts) = isFree k f || any (isFree k) ts
  isFree k (Ind _) = False
  isFree k (Constr _ _ ps as) = or $ map (isFree k) (ps ++ as)

instance IsFree Bind where
  isFree k (Bind _ t) = isFree k t
--  isFree k (NoBind t) = isFree k t
  isFree k (LocalDef _ t1 t2) = isFree k t1 || isFree k t2

isFreeList :: Int -> [Term] -> Bool
isFreeList k = foldrAcc (\n t r -> isFree n t || r) (\n t -> n + 1) k False
