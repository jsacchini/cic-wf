{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}

{-
  TODO
  - Generation of fresh names is slow (not that it matters). See freshName
  - Bound variables that do not appear in the body must be dealt with:
    * for products, replace forall by "->"
    * for functions, replace name by "_"
-}

module Syntax.InternaltoAbstract where

import Control.Monad.Reader

import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Kernel.TCM
import Syntax.Position
import Syntax.Name

class Reify a b | a -> b where
  reify :: (MonadTCM tcm) => a -> tcm b

instance Reify Sort A.Sort where
  reify Prop = return A.Prop
  reify (Type n) = return $ A.Type n

pickFreshName :: (MonadTCM tcm) => Name -> tcm Name
pickFreshName x = do l <- ask
                     return $ freshName (map getName l) x

instance Reify Bind (Name, A.Bind) where
  reify (Bind x t) = do e <- reify t
                        x' <- pickFreshName x
                        return $ (x', A.Bind noRange [x'] e)

instance Reify [Bind] ([Name], [A.Bind]) where
  reify [] = return ([],[])
  reify (b:bs) = do (x, b') <- reify b
                    (xs, bs') <- local (Bind x (Sort Prop):) $ reify bs
                    return (x:xs, b':bs')

instance Reify Term A.Expr where
  reify (Sort s) = do s' <- reify s
                      return $ A.Sort noRange s'
  reify (Pi bs t) = do (xs, bs') <- reify bs
                       e <- local (mkBinds xs++) $ reify t
                       return $ A.Pi noRange bs' e
                         where mkBinds = reverse . map (flip Bind (Sort Prop))
  reify (Bound x n) = do l <- ask
                         -- liftIO $ putStrLn $ "Bound " ++ x ++ " " ++ show n ++ "  -- " ++ show l
                         return $ A.Var noRange (getName (l !! n))
                         -- we assume that vars are in bound
  reify (Var x) = return $ A.Var noRange x
  reify (Lam bs t) = do (xs, bs') <- reify bs
                        e <- local (mkBinds xs++) $ reify t
                        return $ A.Lam noRange bs' e
                          where mkBinds = reverse . map (flip Bind (Sort Prop))
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
