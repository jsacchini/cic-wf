{-# LANGUAGE CPP
  #-}

module Kernel.Whnf where

#include "../undefined.h"
import Utils.Impossible

import Data.List
import Control.Monad.Reader

import Syntax.Internal
import Kernel.TCM

import Syntax.InternaltoAbstract
import Utils.Pretty

class Whnf a where
  whnf :: (MonadTCM tcm) => a -> tcm a

instance Whnf Term where
  whnf (App f ts) =
    do w <- whnf f
       case w of
         Lam bs u -> whnf $ betaRed bs u ts
         Fix n _ _ _ _
           | length ts < n -> return $ App w ts
           | otherwise ->
             do recArg' <- normalForm recArg
                case isConstr recArg' of
                  Just _ -> whnf (muRed w (first ++ recArg' : last))
                  Nothing -> return $ App w ts
           where (first, recArg, last) = splitRecArg [] (n - 1) ts
                 splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                 splitRecArg xs (k + 1) (r : rs) = splitRecArg (r : xs) k rs
         _         -> return $ App w ts
  whnf t@(Var x) =
    do d <- getGlobal x
       case d of
         Definition _ u   -> return u
         Assumption _     -> return t
         _                -> __IMPOSSIBLE__
  whnf t@(Case c) =
    do arg' <- whnf $ caseArg c
       case isConstr arg' of
         Just cid -> whnf $ iotaRed cid (getConstrArgs arg') (caseBranches c)
         Nothing -> return $ Case (c { caseArg = arg' })
  whnf t = return t

-- instance Whnf Bind where
--   whnf (Bind x t) = do w <- whnf t
--                        return $ Bind x w
--   whnf (LocalDef x t u) = do w <- whnf u  -- we only normalize the type
--                              return $ LocalDef x t w


unfoldPi :: (MonadTCM tcm) => Type -> tcm ([Bind], Type)
unfoldPi t =
  do t' <- whnf t
     case t' of
       Pi bs1 t1 -> do (bs2, t2) <- local (reverse bs1++) $ unfoldPi t1
                       return (bs1 ++ bs2, t2)
       t1        -> return ([], t1)


class NormalForm a where
  normalForm :: (MonadTCM tcm) => a -> tcm a

instance NormalForm Bind where
  normalForm (Bind x t) = do t' <- normalForm t
                             return $ Bind x t'
  normalForm (LocalDef x t1 t2) = do t1' <- normalForm t1
                                     t2' <- normalForm t2
                                     return $ LocalDef x t1' t2'

instance NormalForm Term where
  normalForm t@(Sort _) = return t
  normalForm (Pi bs t) = do bs' <- mapM normalForm bs
                            t' <- normalForm t
                            return $ Pi bs' t'
  normalForm t@(Bound _) = do -- traceTCM_ ["Normalizing Bound ", show t]
                              return t
  normalForm t@(Var x) = do -- traceTCM_ ["Normalizing Var ", show x]
                            u <- getGlobal x
                            case u of
                              Definition _ t' -> normalForm  t'
                              Assumption _    -> return t
                              _               -> __IMPOSSIBLE__
  normalForm (Lam bs t) = do bs' <- mapM normalForm bs
                             t' <- normalForm t
                             return $ Lam bs' t'
  normalForm t@(App t1 ts) =
    do -- e <- ask
       -- traceTCM_ ["Normalizing App in ", show e, "\n---\n", show t]
       t1' <- whnf t1
       case t1' of
         Lam bs u  -> do -- traceTCM_ ["Beta Reduction on ",
                                    -- "( fun ", show bs, " => ", show u, ")\non\n",
                                    -- show ts]
                         normalForm $ betaRed bs u ts
         App u1 us -> do ts' <- mapM normalForm ts
                         return $ buildApp u1 (us ++ ts')
         Fix n _ _ _ _
           | length ts < n -> do -- traceTCM_ ["Fix without enough args ", show (length ts), " < ", show n]
                                 ts' <- mapM normalForm ts
                                 return $ App t1' ts'
           | otherwise ->
             do -- traceTCM_ ["Fix enough args\nFirst ", show first, "\nRec ", show recArg, "\nLast ", show last]
                recArg' <- normalForm recArg
                case isConstr recArg' of
                  Just _ -> do -- traceTCM_ ["Mu Reduction ",
                               --            show t1', "\non\n",
                               --            show (first ++ recArg' : last)]
                               normalForm (muRed t1' (first ++ recArg' : last))
                  Nothing -> do -- traceTCM_ ["No recursion arg = ", show recArg']
                                first' <- mapM normalForm first
                                last'  <- mapM normalForm last
                                return $ buildApp t1' (first' ++ recArg' : last')
           where (first, recArg, last) = splitRecArg [] (n - 1) ts
                 splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                 splitRecArg xs (k + 1) (r : rs) = splitRecArg (r : xs) k rs
         _         -> do -- traceTCM_ ["Not handled application", show t1']
                         ts' <- mapM normalForm ts
                         return $ buildApp t1' ts'
  normalForm t@(Ind _ _) = do -- traceTCM_ ["Normalizing Ind ", show t]
                              return t
  normalForm t@(Case c) =
    do arg' <- normalForm $ caseArg c
       case isConstr arg' of
         Just cid -> do -- traceTCM_ ["Iota Reduction ",
                        --            show cid, " ", show (getConstrArgs arg'),
                        --            "\nwith branches\n",
                        --           show (caseBranches c)]
                        normalForm $ iotaRed cid (getConstrArgs arg') (caseBranches c)
         Nothing -> do -- traceTCM_ ["Case in normal form ", show t]
                       ret' <- normalForm (caseTpRet c)
                       branches' <- mapM normalForm (caseBranches c)
                       return $ Case (c { caseArg      = arg',
                                          caseTpRet    = ret',
                                          caseBranches = branches' })
  normalForm t@(Constr x i ps as) =
    do -- traceTCM_ ["Normalizing constr ", show t]
       ps' <- mapM normalForm ps
       as' <- mapM normalForm as
       return $ Constr x i ps' as'
  normalForm t@(Fix k nm bs tp body) =
    do -- traceTCM_ ["Normalizing fix ", show t]
       bs' <- mapM normalForm bs
       tp' <- normalForm tp
       body' <- normalForm body
       return $ Fix k nm bs' tp' body'


instance NormalForm Branch where
  normalForm (Branch nm cid xs body) =
    do body' <- normalForm body
       return $ Branch nm cid xs body'


-- | 'betaRed' bs body args  performs several beta reductions on the term
--   App (Lam bs body) args.
--
--   The number of beta reductions applied is min (length bs, length args)
betaRed :: [Bind] -> Term -> [Term] -> Term
betaRed [] body [] = body
betaRed [] body args = App body args
betaRed binds body [] = Lam binds body
betaRed (Bind _ _:bs) body (a:as) = betaRed (subst a bs) (substN (length bs) a body) as
betaRed (LocalDef _ _ _:_) _ _ = __IMPOSSIBLE__


-- | 'iotaRed' @cid@ @args@ @branches@ performs a iota reduction where the
--   argument of the case is a constructor with id @cid@ applied to arguments
--   @args@ (parameters are not needed to perform iota reduction) and @branches@
--   branches of the case
iotaRed :: Int -> [Term] -> [Branch] -> Term
iotaRed cid args branches =
  case find ( (==cid) . brConstrId ) branches of
    Just br -> foldr subst (brBody br) args
    Nothing -> __IMPOSSIBLE__

-- | 'muRed' @fix@ @args@ unfolds the fixpoint and applies it to the arguments
--   @args@ shoudl have a length greater or equal than the recursive argument of
--   fix and the recursive argument should be in constructor form
muRed :: Term -> [Term] -> Term
muRed t@(Fix _ _ _ _ body) args = buildApp (subst t body) args
muRed _ _ = __IMPOSSIBLE__


-- Neutral term
-- We assume that all global definitions have been unfolded (see Var case)
neutral :: Term -> Bool
neutral (Sort _) = False
neutral (Pi _ _) = False
neutral (Bound _) = True
neutral (Var _) = True -- we assume that this Var corresponds to an assumption
neutral (Lam _ _) = False
neutral (App (Fix n _ _ _ _) ts) | length ts < n = False
                                 | otherwise = neutral $ ts !! (n - 1)
neutral (App t _) = neutral t
neutral (Constr _ _ _ _) = False
neutral (Fix _ _ _ _ _) = False
neutral (Case c) = neutral $ caseArg c
neutral (Ind _ _) = False

