{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies
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

import Syntax.Internal as I
import qualified Syntax.Abstract as A
import Syntax.ScopeMonad
import Syntax.Position
import Syntax.Common
import Utils.Misc

class Reify a b | a -> b where
  reify :: (ScopeMonad sm) => a -> sm b


freshName :: (ScopeMonad sm) => Name -> sm Name
freshName x | isNull x  = return $ Id "_"
            | otherwise = do xs <- getLocalNames
                             return $ doFreshName xs x
              where
                doFreshName xs y | y `notElem` xs = y
                                 | otherwise = trySuffix xs y (0 :: Int)
                trySuffix xs y n | addSuffix y n `notElem` xs = addSuffix y n
                                 | otherwise = trySuffix xs y (n+1)
                addSuffix (Id x) n = Id $ x ++ show n


freshNameList :: (ScopeMonad sm) => [Name] -> sm [Name]
freshNameList []     = return []
freshNameList (x:xs) = do x' <- freshName x
                          xs' <- fakeBinds x' $ freshNameList xs
                          return $ x' : xs'


reifyPiBinds :: (ScopeMonad sm) => [Bind] -> Term -> sm A.Expr
reifyPiBinds = rP []
  where
    rP :: (ScopeMonad sm) => [A.Bind] -> [Bind] -> Term -> sm A.Expr
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

reifyLamBinds :: (ScopeMonad sm) => [Bind] -> Term -> sm A.Expr
reifyLamBinds = rL []
  where
    rL :: (ScopeMonad sm) => [A.Bind] -> [Bind] -> Term -> sm A.Expr
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
  reify (Pi bs t) = do traceSM $ "printing " ++ show (Pi bs t)
                       traceSM $ "reifyBinds " ++ show bs
                       reifyPiBinds bs t
  reify (Bound n) = do xs <- getLocalNames
                       l <- ask
                       when (n >= length xs) $ get >>= \st -> traceSM $ "InternaltoAbstract Bound " ++ " " ++ show n ++ "  -- " ++ show l ++ " \n\n" ++ show st
                       return $ A.Ident noRange (xs !! n)
  reify (Var x) = return $ A.Ident noRange x
  reify (Lam bs t) = reifyLamBinds bs t
  reify (App t ts) = do e <- reify t
                        es <- mapM reify ts
                        return $ mkApp e es
                          where mkApp = foldl (A.App noRange)
  reify (Ind i) = return $ A.Ind noRange Empty i
  reify (Constr x indId ps as) =
    do ps' <- mapM reify ps
       as' <- mapM reify as
       return $ A.Constr noRange x indId ps' as'
  reify (Fix num f args tp body) =
    do tp'   <- reify (buildPi args tp)
       f'    <- freshName f
       body' <- fakeBinds f' $ reify body
       return $ A.Fix (A.FixExpr noRange num f tp' body')
  reify (Case c) = fmap A.Case $ reify c


instance Reify CaseTerm A.CaseExpr where
  reify (CaseTerm arg _ tpRet branches) =
    do arg' <- reify arg
       ret' <- reify tpRet
       branches' <- mapM reify branches
       return $
         A.CaseExpr noRange arg' Nothing Nothing Nothing (Just ret') branches'

instance Reify Branch A.Branch where
  reify (Branch nmConstr idConstr nmArgs body) =
    do nmArgs' <- freshNameList nmArgs
       body' <- fakeBinds nmArgs' $ reify body
       return $ A.Branch noRange nmConstr idConstr nmArgs' body'


instance Reify Name A.Declaration where
  reify x =
    do g <- getGlobal x
       case g of
         I.Definition t1 t2 -> do e1 <- reify t1
                                  e2 <- reify t2
                                  return $ A.Definition noRange x (Just e1) e2
         I.Assumption t -> do e <- reify t
                              return $ A.Assumption noRange x e
         t@(I.Inductive {}) ->
           do traceSM $ "data " ++ show x ++ " : " ++ show t
              return $ A.Inductive noRange (A.InductiveDef x [] (A.Sort noRange Prop) [])
           -- COMPLETE THIS CASE
         t@(Constructor _ _ _ _ _) ->
           do traceSM $ "constructor " ++ show x ++ " : " ++ show t
              return $ A.Assumption noRange x (A.Sort noRange Prop)


-- | Free bound variables

class IsFree a where
  isFree :: Int -> a -> Bool

instance IsFree Term where
  isFree _ (Sort _) = False
  isFree k (Pi [] t) = isFree k t
  isFree k (Pi (b:bs) t) = isFree k b || isFree (k+1) (Pi bs t)
  isFree k (Bound n) = k == n
  isFree _ (Var _) = False
  isFree k (Lam [] t) = isFree k t
  isFree k (Lam (b:bs) t) = isFree k b || isFree (k+1) (Lam bs t)
  isFree k (App f ts) = isFree k f || any (isFree k) ts
  isFree _ (Ind _) = False
  isFree k (Constr _ _ ps as) = any (isFree k) (ps ++ as)
  isFree k (Fix _ _ bs tp body) = isFree k (buildPi bs tp) || isFree (k+1) body
  isFree k (Case c) = isFree k c

instance IsFree CaseTerm where
  isFree k (CaseTerm arg _ tpRet branches) =
    isFree k arg || isFree k tpRet || any (isFree k) branches

instance IsFree Branch where
  isFree k (Branch _ _ nmArgs body) =
    isFree (k + length nmArgs) body


instance IsFree Bind where
  isFree k (Bind _ t) = isFree k t
  isFree k (LocalDef _ t1 t2) = isFree k t1 || isFree k t2

isFreeList :: Int -> [Term] -> Bool
isFreeList k = foldrAcc (\n t r -> isFree n t || r) (\n _ -> n + 1) k False
