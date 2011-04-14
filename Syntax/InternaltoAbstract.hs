{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

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
  reify Prop = return $ A.Prop
  reify (Type n) = return $ A.Type n

instance Reify Bind A.Bind where
  reify (Bind x t) = do e <- reify t
                        return $ A.Bind noRange [x] e

instance Reify Term A.Expr where
  reify (Sort s) = do s' <- reify s
                      return $ A.Sort noRange s'
  reify (Pi bs t) = do bs' <- mapM reify bs
                       e <- reify t
                       return $ A.Pi noRange bs' e
  reify (Bound x n) = do l <- ask
                         return $ A.Var noRange (getName (l !! n))
                         -- we assume that vars are in bound
  reify (Var x) = return $ A.Var noRange x
  reify (Lam bs t) = do bs' <- mapM reify bs
                        e <- reify t
                        return $ A.Lam noRange bs' e
  reify (App t ts) = do e <- reify t
                        es <- mapM reify ts
                        return $ mkApp e es
                          where mkApp = foldl (A.App noRange)
  reify (Ind i) = return $ A.Ind noRange i

