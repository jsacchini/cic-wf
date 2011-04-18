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
import Syntax.Name
import Syntax.Scope (fakeBindsIn)
import Utils.Misc

class Reify a b | a -> b where
  reify :: (MonadTCM tcm) => a -> tcm b

instance Reify Sort A.Sort where
  reify Prop = return A.Prop
  reify (Type n) = return $ A.Type n

pickFreshName :: (MonadTCM tcm) => Name -> tcm Name
pickFreshName x  = do l <- ask
                      return $ freshName (map getName l) x

pickFreshNames :: (MonadTCM tcm) => [Name] -> tcm [Name]
pickFreshNames []     = return []
pickFreshNames (x:xs) = do x' <- pickFreshName x
                           xs' <- fakeBindsIn [x'] $ pickFreshNames xs
                           return $ x' : xs'

-- instance Reify Bind (Name, A.Expr) where
--   reify (Bind x t) = do e <- reify t
--                         x' <- pickFreshName x
--                         return $ (x', e)

-- Ugly
-- instance Reify ([Bind],Term) ([Name], [A.Bind]) where
--   reify [] = return ([],[])
--   reify (b:bs) = do (x, b') <- reify b
--                     (xs, bs') <- local (Bind x (Sort Prop):) $ reify bs
--                     return (x:xs, b':bs')

reifyBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm ([Name], [A.Bind])
reifyBinds bs t = reify_ (groupBinds $ findFree bs t)
  where findFree :: [Bind] -> Term -> [Bind]
        findFree [] t = []
        findFree (b@(NoBind t1):bs) t = NoBind t1 : findFree bs t
        findFree (b@(Bind x t1):bs) t
          | not $ isFreeList 0 (map bind bs ++ [t]) = NoBind t1 : findFree bs t
          | otherwise                               = b : findFree bs t
        groupBinds :: [Bind] -> [([Name], Type)]
        groupBinds = foldr f []
          where f (NoBind t) rs = ([], t) : rs
                f (Bind x t) [] = [([x],t)]
                f (Bind x t) r@((xs,t'):rs) | t == t'   = (x:xs,t') : rs
                                            | otherwise = ([x],t) : r
        reify_ :: (MonadTCM tcm) => [([Name], Type)] -> tcm ([Name], [A.Bind])
        reify_ [] = return ([], [])
        reify_ ((xs,t):ts) =
          do xs' <- pickFreshNames xs
             e <- reify t
             (ys, bs) <- fakeBindsIn (reverse (mkNameIfEmpty xs')) $ reify_ ts
             if null xs
               then return ("_" : ys, A.NoBind e:bs)
               else return (xs' ++ ys, A.Bind noRange xs' e : bs)
            where mkNameIfEmpty [] = ["_"]
                  mkNameIfEmpty xs = xs

instance Reify Term A.Expr where
  reify (Sort s) = do s' <- reify s
                      return $ A.Sort noRange s'
  reify (Pi bs t) = do -- liftIO $ putStrLn $ "printing " ++ show (Pi bs t)
                       -- liftIO $ putStrLn $ "reifyBinds " ++ show bs
                       (xs, bs') <- reifyBinds bs t
                       -- liftIO $ putStrLn $ "reifiedBinds " ++ show bs'
                       e <- fakeBindsIn (reverse xs) $ reify t
                       return $ A.Pi noRange bs' e
  reify (Bound n) = do l <- ask
                       when (n >= length l) $ get >>= \st -> liftIO $ putStrLn $ "Bound " ++ " " ++ show n ++ "  -- " ++ show l ++ " \n\n" ++ show st
                       return $ A.Var noRange (getName (l !! n))
                       -- return $ A.Var noRange "AA"
                         -- we assume that vars are in bound
  reify (Var x) = return $ A.Var noRange x
  reify (Lam bs t) = do (xs, bs') <- reifyBinds bs t
                        e <- fakeBindsIn (reverse xs) $ reify t
                        return $ A.Lam noRange bs' e
  reify (App t ts) = do e <- reify t
                        es <- mapM reify ts
                        return $ mkApp e es
                          where mkApp = foldl (A.App noRange)
  reify (Ind i) = return $ A.Ind noRange i

instance Reify Name A.Declaration where
  reify x = do g <- getGlobal x
               case g of
                 I.Definition t1 t2 -> do e1 <- reify t1
                                          e2 <- reify t2
                                          return $ A.Definition noRange x (Just e1) e2
                 I.Assumption t -> do e <- reify t
                                      return $ A.Assumption noRange x e


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

instance IsFree Bind where
  isFree k (Bind _ t) = isFree k t
  isFree k (NoBind t) = isFree k t
  isFree k (LocalDef _ t1 t2) = isFree k t1 || isFree k t2

isFreeList :: Int -> [Term] -> Bool
isFreeList k = foldrAcc (\n t r -> isFree n t || r) (\n t -> n + 1) k False
