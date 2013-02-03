{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
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

#include "../undefined.h"
import Utils.Impossible

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

freshNameList :: (MonadTCM tcm) => [Name] -> tcm [Name]
freshNameList []     = return []
freshNameList (x:xs) = do x' <- freshenName x
                          xs' <- fakeBinds x' $ freshNameList xs
                          return $ x' : xs'


reifyPiBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm A.Expr
reifyPiBinds = rP []
  where
    rP :: (MonadTCM tcm) => [A.Bind] -> [Bind] -> Term -> tcm A.Expr
    rP [] [] t                  = reify t
    rP bs [] t                  = do e <- reify t
                                     return $ A.Pi noRange (reverse bs) e
    rP [] bs@(Bind x impl t1 Nothing:bs') t2
      | notFree bs' t2 =
        do e1 <- reify t1
           e2 <- fakeBinds noName $ rP [] bs' t2
           return $ A.Arrow noRange e1 e2
      | otherwise     =
          do e1 <- reify t1
             x' <- freshenName x
             fakeBinds x' $ rP [A.Bind noRange impl [x'] e1] bs' t2
    -- TODO: check implicit printing
    rP bs1@(A.Bind _ impl1 xs e1:bs1') bs2@(Bind y impl2 t1 Nothing:bs2') t2
      | notFree bs2' t2 =
        do e2 <- rP [] bs2 t2
           return $ A.Pi noRange (reverse bs1) e2
      | otherwise     =
          do e1' <- reify t1
             y' <- freshenName y
             if e1 == e1' && impl1 == impl2
               then fakeBinds y' $ rP (A.Bind noRange impl1 (xs++[y']) e1:bs1') bs2' t2
               else fakeBinds y' $ rP (A.Bind noRange impl2 [y'] e1':bs1) bs2' t2
    rP _ _ _ = error "complete rP"
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])

reifyLamBinds :: (MonadTCM tcm) => [Bind] -> Term -> tcm A.Expr
reifyLamBinds = rL []
  where
    rL :: (MonadTCM tcm) => [A.Bind] -> [Bind] -> Term -> tcm A.Expr
    rL bs [] t                  = do e <- reify t
                                     return $ A.Lam noRange (reverse bs) e
    rL [] (Bind x impl t1 Nothing:bs') t2 =
      do e1 <- reify t1
         x' <- if notFree bs' t2 then return (Id "_") else freshenName x
         fakeBinds x' $ rL [A.Bind noRange impl [x'] e1] bs' t2
    -- TODO: check implicit printing
    rL bs1@(A.Bind _ impl1 xs e1:bs1') (Bind y impl2 t1 Nothing:bs2') t2 =
      do e1' <- reify t1
         y' <- if notFree bs2' t2 then return (Id "_") else freshenName y
         if e1 == e1' && impl1 == impl2
           then fakeBinds y' $ rL (A.Bind noRange impl1 (xs++[y']) e1:bs1') bs2' t2
           else fakeBinds y' $ rL (A.Bind noRange impl2 [y'] e1':bs1) bs2' t2
    rL _ _ _ = error "Complete rL"
    notFree :: [Bind] -> Term -> Bool
    notFree bs t = not $ isFreeList 0 (map bind bs ++ [t])


-- TODO: add option to print universes. If set, reify should return (Type (Just n))
instance Reify Sort A.Sort where
  reify Prop     = return A.Prop
  reify (Type k) = return (A.Type (Just (fromEnum k)))

instance Reify Term A.Expr where
  reify (Sort s) = do s' <- reify s
                      return $ A.Sort noRange s'
  reify (Pi ctx t) = do -- traceTCM $ "printing " ++ show (Pi bs t)
                             -- traceTCM $ "reifyBinds " ++ show bs
                       reifyPiBinds (Fold.toList ctx) t
  reify (Bound n) = do xs <- getLocalNames
                       l <- ask
                       -- when (n >= length xs) $ get >>= \st -> traceTCM $ "InternaltoAbstract Bound " ++ " " ++ show n ++ "  -- " ++ show l ++ " \n\n" ++ show st
                       if (n >= length xs)
                         then return $ A.Bound noRange (Id $ "ERROR "++show n) n
                         else return $ A.Bound noRange (xs !! n) n
  reify (Meta k) = do (Just g) <- getGoal k
                      case goalTerm g of
                        Nothing -> return $ A.Meta noRange (Just (fromEnum k))
                        Just t  -> reify t
  reify (Lam ctx t) = reifyLamBinds (Fold.toList ctx) t
  reify (Fix k num f args tp body) =
    do tp'   <- reify (mkPi args tp)
       f'    <- freshenName f
       body' <- fakeBinds f' $ reify body
       return $ A.Fix (A.FixExpr noRange k num f tp' body')
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
            reifyCtx (ExtendCtx (Bind x impl t _) ctx') args =
              do t' <- reify t
                 x' <- freshenName x
                 (bs, args') <- fakeBinds x' $ reifyCtx ctx' args
                 return (A.Bind noRange impl [x'] t' : bs, args')

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
           return $ A.Inductive noRange (A.InductiveDef x (I.indKind t) [] (A.mkProp noRange) [])
           -- COMPLETE THIS CASE
         t@(Constructor _ _ _ _ _ _) -> do
           return $ A.Assumption noRange x (A.mkProp noRange)


--- for debugging

instance Reify [Bind] [A.Bind] where
  reify [] = return []
  reify (b:c) =
    do b' <- rb b
       -- x <- freshenName (bindName b)
       c' <- fakeBinds [bindName b] $ reify c
       return (b':c')
         where rb (Bind x impl t Nothing) =
                 do t' <- reify t
                    return $ A.Bind noRange impl [x] t'
               rb (Bind x impl t (Just _)) = __IMPOSSIBLE__
