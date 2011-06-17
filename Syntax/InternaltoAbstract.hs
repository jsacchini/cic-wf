{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
TypeSynonymInstances, FlexibleInstances
  #-}

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

import Data.Traversable (traverse)
import qualified Data.Foldable as Fold

import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Kernel.TCM
import Syntax.Position
import Syntax.Common
import Utils.Misc

class Reify a b | a -> b where
  reify :: (MonadTCM tcm) => a -> tcm b

freshName :: (MonadTCM tcm) => Name -> tcm Name
freshName x | isNull x  = return $ Id "_"
            | otherwise = do xs <- getLocalNames
                             return $ doFreshName xs x
              where
                doFreshName xs y | y `notElem` xs = y
                                 | otherwise = trySuffix xs y (0 :: Int)
                trySuffix xs y n | addSuffix y n `notElem` xs = addSuffix y n
                                 | otherwise = trySuffix xs y (n+1)
                addSuffix (Id x) n = Id $ x ++ show n


freshNameList :: (MonadTCM tcm) => [Name] -> tcm [Name]
freshNameList []     = return []
freshNameList (x:xs) = do x' <- freshName x
                          xs' <- fakeBinds x' $ freshNameList xs
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
        do e1 <- reify t1
           e2 <- fakeBinds noName $ rP [] bs' t2
           return $ A.Arrow noRange e1 e2
      | otherwise     =
          do e1 <- reify t1
             x' <- freshName x
             fakeBinds x' $ rP [A.Bind noRange [x'] e1] bs' t2
    rP bs1@(A.Bind _ xs e1:bs1') bs2@(Bind y t1:bs2') t2
      | notFree bs2' t2 =
        do e2 <- rP [] bs2 t2
           return $ A.Pi noRange (reverse bs1) e2
      | otherwise     =
          do e1' <- reify t1
             y' <- freshName y
             if e1 == e1'
               then fakeBinds y' $ rP (A.Bind noRange (xs++[y']) e1:bs1') bs2' t2
               else fakeBinds y' $ rP (A.Bind noRange [y'] e1':bs1) bs2' t2
    rP _ _ _ = error "complete rP"
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])

reifyLamBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm A.Expr
reifyLamBinds = rL []
  where
    rL :: (MonadTCM tcm) => [A.Bind] -> [Bind] -> Term -> tcm A.Expr
    rL bs [] t                  = do e <- reify t
                                     return $ A.Lam noRange (reverse bs) e
    rL [] (Bind x t1:bs') t2 =
      do e1 <- reify t1
         x' <- if notFree bs' t2 then return (Id "_") else freshName x
         fakeBinds x' $ rL [A.Bind noRange [x'] e1] bs' t2
    rL bs1@(A.Bind _ xs e1:bs1') (Bind y t1:bs2') t2 =
      do e1' <- reify t1
         y' <- if notFree bs2' t2 then return (Id "_") else freshName y
         if e1 == e1'
           then fakeBinds y' $ rL (A.Bind noRange (xs++[y']) e1:bs1') bs2' t2
           else fakeBinds y' $ rL (A.Bind noRange [y'] e1':bs1) bs2' t2
    rL _ _ _ = error "Complete rL"
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])


instance Reify Term A.Expr where
  reify (Sort s) = return $ A.Sort noRange s
  reify (Pi ctx t) = do -- traceTCM $ "printing " ++ show (Pi bs t)
                             -- traceTCM $ "reifyBinds " ++ show bs
                       reifyPiBinds (Fold.toList ctx) t
  reify (Bound n) = do xs <- getLocalNames
                       l <- ask
                       -- when (n >= length xs) $ get >>= \st -> traceTCM $ "InternaltoAbstract Bound " ++ " " ++ show n ++ "  -- " ++ show l ++ " \n\n" ++ show st
                       if (n >= length xs)
                         then return $ A.Bound noRange (Id $ "ERROR "++show n) n
                         else return $ A.Bound noRange (xs !! n) n
  reify (Lam ctx t) = reifyLamBinds (Fold.toList ctx) t
  reify (Fix num f args tp body) =
    do tp'   <- reify (mkPi args tp)
       f'    <- freshName f
       body' <- fakeBinds f' $ reify body
       return $ A.Fix (A.FixExpr noRange num f tp' body')
  reify (Case c) = fmap A.Case $ reify c
  -- Special case for reification of natural numbers
  -- case O
  reify (Constr (Id "O") cid [] []) = return $ A.Number noRange 0
  reify (Var (Id "O")) = return $ A.Number noRange 0
  reify (Ind _ (Id "O")) = return $ A.Number noRange 0
  -- case S
  reify (Constr (Id "S") cid [t] []) =
    do t' <- reify t
       return $ case t' of
         A.Number noRange k -> A.Number noRange (k + 1)
         _                  -> A.Constr noRange (Id "S") cid [t'] []
  reify (Constr (Id "S") cid [] [t]) =
    do t' <- reify t
       return $ case t' of
         A.Number noRange k -> A.Number noRange (k + 1)
         _                  -> A.Constr noRange (Id "S") cid [] [t']
  reify (App (Var (Id "S")) [t]) =
    do t' <- reify t
       return $ case t' of
         A.Number noRange k -> A.Number noRange (k + 1)
         _                  -> A.App noRange (A.Ident noRange (Id "S")) t'
  reify (App (Ind a (Id "S")) [t]) =
    do t' <- reify t
       return $ case t' of
         A.Number noRange k -> A.Number noRange (k + 1)
         _                  -> A.App noRange (A.Ind noRange a (Id "S")) t'
  -- General case for Var, App, Ind, and Constr
  reify (Constr x indId ps as) =
    do ps' <- mapM reify ps
       as' <- mapM reify as
       return $ A.Constr noRange x indId ps' as'
  reify (App t ts) = do e <- reify t
                        es <- mapM reify ts
                        return $ mkApp e es
                          where mkApp = foldl (A.App noRange)
  reify (Var x) = return $ A.Ident noRange x
  reify (Ind a i) = return $ A.Ind noRange a i

-- TODO: print properly the names of CaseIn: do not show variables not used
instance Reify CaseTerm A.CaseExpr where
  reify (CaseTerm arg _ asName cin tpRet branches) =
    do arg' <- reify arg
       cin' <- traverse reify cin
       ret' <- fakeBinds cin' $ fakeBinds asName $ reify tpRet
       branches' <- mapM (fakeBinds cin . reify) branches
       return $
         A.CaseExpr noRange arg' asName cin'  Nothing (Just ret') branches'

instance Reify CaseIn A.CaseIn where
  reify (CaseIn ctx nmInd args) =
    do (ctx', args') <- reifyCtx ctx args
       return $ A.CaseIn noRange ctx' nmInd args'
      where reifyCtx EmptyCtx args = do args' <- mapM reify args
                                        return ([], args')
            reifyCtx (ExtendCtx (Bind x t) ctx') args =
              do t' <- reify t
                 x' <- freshName x
                 (bs, args') <- fakeBinds x' $ reifyCtx ctx' args
                 return (A.Bind noRange [x'] t' : bs, args')

instance Reify Branch A.Branch where
  reify (Branch nmConstr idConstr nmArgs body whSubst) =
    do nmArgs' <- freshNameList nmArgs
       body' <- fakeBinds nmArgs' $ reify body
       whSubst' <- fakeBinds nmArgs' $ traverse reify whSubst
       return $ A.Branch noRange nmConstr idConstr nmArgs' body' whSubst'

instance Reify Subst A.Subst where
  reify (Subst sg) =
    do sg' <- mapM reifyAssign sg
       return $ A.Subst sg'
      where reifyAssign (k, t) = do xs <- getLocalNames
                                    e <- reify t
                                    return $ A.Assign noRange (xs !! k) k e

instance Reify Name A.Declaration where
  reify x =
    do g <- getGlobal x
       case g of
         I.Definition t1 t2 -> do e1 <- reify t1
                                  e2 <- reify t2
                                  return $ A.Definition noRange x (Just e1) e2
         I.Assumption t -> do e <- reify t
                              return $ A.Assumption noRange x e
         t@(I.Inductive {}) -> do
           return $ A.Inductive noRange (A.InductiveDef x [] (A.Sort noRange Prop) [])
           -- COMPLETE THIS CASE
         t@(Constructor _ _ _ _ _ _) -> do
           return $ A.Assumption noRange x (A.Sort noRange Prop)


--- for debugging

instance Reify [Bind] [A.Bind] where
  reify [] = return []
  reify (b:c) =
    do b' <- rb b
       -- x <- freshName (bindName b)
       c' <- fakeBinds [bindName b] $ reify c
       return (b':c')
         where rb (Bind x t) = do t' <- reify t
                                  return $ A.Bind noRange [x] t'
               rb (LocalDef x t1 t2) = do t1' <- reify t1
                                          t2' <- reify t2
                                          return $ A.Bind noRange [x] (A.Ann noRange t1' t2')
