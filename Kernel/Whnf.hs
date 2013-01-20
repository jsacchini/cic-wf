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

{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances
  #-}

module Kernel.Whnf where

#include "../undefined.h"
import Utils.Impossible

import Data.List
import qualified Data.Foldable as Fold
import Control.Monad.Reader

import Syntax.Common
import Syntax.Internal as I
import Syntax.InternaltoAbstract
import Kernel.TCM
import Kernel.PrettyTCM

import Utils.Pretty

class Whnf a where
  whnf :: (MonadTCM tcm) => a -> tcm a

instance Whnf Term where
  whnf (App f ts) =
    do w <- whnf f
       case w of
         Lam ctx u -> whnf $ betaRed ctx u ts
         Fix I n _ _ _ _
           | length ts < n -> return $ App w ts
           | otherwise ->
             do recArg' <- normalForm recArg
                case recArg' of
                  Constr {} -> whnf (muRed w (first ++ recArg' : last))
                  _ -> return $ App w ts
           where (first, recArg, last) = splitRecArg [] (n - 1) ts
                 splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                 splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
         _         -> return $ App w ts
  whnf t@(Bound k) = do len <- localLength
                        when (k >= len) $ error $ "Whnf " ++ show k ++ "\nin "-- ++ show e
                        b <- localGet k
                        case bindDef b of
                          Nothing -> return t
                          Just t' -> whnf (I.lift (k+1) 0 t')
  whnf t@(Var x) =
    do d <- getGlobal x
       case d of
         Definition _ u   -> return u
         Assumption _     -> return t
         _                -> __IMPOSSIBLE__
  whnf t@(Case c) =
    do arg' <- whnf $ caseArg c
       case arg' of
         Constr _ _ (_,cid) _ cArgs -> whnf $ iotaRed cid cArgs (caseBranches c)
         _ -> case isCofix arg' of
                Just (_, body, cofix, args) -> whnf $ Case (c { caseArg = App (subst cofix body) args })
                Nothing -> return $ Case (c { caseArg = arg' })
  whnf t = return t

-- instance Whnf Bind where
--   whnf (Bind x t) = do w <- whnf t
--                        return $ Bind x w
--   whnf (LocalDef x t u) = do w <- whnf u  -- we only normalize the type
--                              return $ LocalDef x t w


-- isCofix (App (cofix f:T := M) ts) = Just (f, T, M, cofix f := M, ts)
isCofix :: Term -> Maybe (Bind, Term, Term, [Term])
isCofix t@(Fix CoI _ f ctx tp body)          = Just (mkBind f (mkPi ctx tp), body, t, [])
isCofix (App t@(Fix CoI _ f ctx tp body) ts) = Just (mkBind f (mkPi ctx tp), body, t, ts)
isCofix _                                    = Nothing

unfoldPi :: (MonadTCM tcm) => Type -> tcm (Context, Type)
unfoldPi t =
  do t' <- whnf t
     case t' of
       Pi ctx1 t1 -> do (ctx2, t2) <- pushCtx ctx1 $ unfoldPi t1
                        t2' <- pushCtx (ctx1 +: ctx1) $ whnf t2
                        return (ctx1 +: ctx2, t2')
       _          -> return (empCtx, t')


class NormalForm a where
  normalForm :: (MonadTCM tcm) => a -> tcm a

instance NormalForm a => NormalForm (Maybe a) where
  normalForm Nothing = return Nothing
  normalForm (Just x) = do y <- normalForm x
                           return $ Just y

instance NormalForm a => NormalForm [a] where
  normalForm [] = return []
  normalForm (x:xs) = do y <- normalForm x
                         ys <- normalForm xs
                         return (y:ys)

instance NormalForm Sort where
  normalForm x = return x

instance NormalForm Bind where
  normalForm (Bind x impl t def) = do t' <- normalForm t
                                      def' <- normalForm def
                                      return $ Bind x impl t' def'

instance NormalForm Context where
  normalForm EmptyCtx = return EmptyCtx
  normalForm (ExtendCtx b c) = do b' <- normalForm b
                                  c' <- pushBind b' $ normalForm c
                                  return (b' <| c)

instance NormalForm Term where
  normalForm (Sort s) = do s' <- normalForm s
                           return $ Sort s'
  normalForm (Pi c t) = do c' <- normalForm c
                           t' <- pushCtx c $ normalForm t
                           return $ Pi c' t'
  normalForm t@(Bound k) = do e <- ask
                              when (k >= length (unEnv e)) $ error $ "normalform out of bound: " ++ show k ++ "  " ++ show e
                              case bindDef (unEnv e !! k) of
                                Nothing -> return t
                                Just t' -> normalForm (I.lift (k+1) 0 t')
  normalForm t@(Var x) = do traceTCM 30 $ hsep [text "Normalizing Var ", prettyPrintTCM x]
                            u <- getGlobal x
                            case u of
                              Definition _ t' ->
                                do
                                  traceTCM 30 $ hsep [text "global", prettyPrintTCM t']
                                  normalForm t'
                              Assumption _    -> return t
                              _               -> __IMPOSSIBLE__
  normalForm (Lam c t) = do c' <- normalForm c
                            t' <- pushCtx c $ normalForm t
                            return $ Lam c' t'
  normalForm t@(App t1 ts) =
    do e <- ask
       traceTCM 30 $ hsep [text "Normalizing App in ", prettyPrintTCM e,
                           text ":", prettyPrintTCM t]
       t1' <- whnf t1
       case t1' of
         Lam ctx u  ->
           do traceTCM 30 $ (hsep [text "Beta Reduction on ",
                                   prettyPrintTCM t1',
                                   text " and ",
                                   prettyPrintTCM ts]
                             $$ hsep [text "reduces to ", prettyPrintTCM (betaRed ctx u ts)])
              normalForm $ betaRed ctx u ts
         App u1 us -> do ts' <- mapM normalForm ts
                         us' <- mapM normalForm us
                         return $ mkApp u1 (us' ++ ts')
         Fix I n _ _ _ _
           | length ts < n -> do -- traceTCM_ ["Fix without enough args ", show (length ts), " < ", show n]
                                 ts' <- mapM normalForm ts
                                 return $ App t1' ts'
           | otherwise ->
             do -- traceTCM_ ["Fix enough args\nFirst ", show first, "\nRec ", show recArg, "\nLast ", show last]
                recArg' <- normalForm recArg
                case recArg' of
                  Constr {} ->
                            do -- traceTCM_ ["Mu Reduction ",
                               --            show t1', "\non\n",
                               --            show (first ++ recArg' : last)]
                               normalForm (muRed t1' (first ++ recArg' : last))
                  _    -> do -- traceTCM_ ["No recursion arg = ", show recArg']
                             first' <- mapM normalForm first
                             last'  <- mapM normalForm last
                             return $ mkApp t1' (first' ++ recArg' : last')
           where (first, recArg, last) = splitRecArg [] (n - 1) ts
                 splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                 splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
         _         -> do -- traceTCM_ ["Not handled application", show t1']
                         ts' <- mapM normalForm ts
                         return $ mkApp t1' ts'
  normalForm t@(Ind _ _) = do -- traceTCM_ ["Normalizing Ind ", show t]
                              return t
  normalForm t@(Case c) =
    do traceTCM 30 $ (hsep [text "Normalizing Case in ", prettyPrintTCM t]
                      $$ hsep [text "arg ", prettyPrintTCM (caseArg c)])
       arg' <- normalForm $ caseArg c
       case arg' of
         Constr _ _ (_,cid) _ cArgs ->
                     do -- traceTCM_ ["Iota Reduction ",
                        --            show cid, " ", show cArgs,
                        --            "\nwith branches\n",
                        --           show (caseBranches c)]
                        normalForm $ iotaRed cid cArgs (caseBranches c)
         _ -> case isCofix arg' of
                Just (bind, body, cofix, args) ->
                  do
                    traceTCM 30 $ vcat [text "normal form case " <> prettyPrintTCM t,
                                        text "body " <> pushBind bind (prettyPrintTCM body),
                                        text "cofix " <> prettyPrintTCM cofix,
                                        text "args " <> prettyPrintTCM args]
                    normalForm $ Case (c { caseArg = App (subst cofix body) args })
                Nothing ->
                  do -- traceTCM_ ["Case in normal form ", show t]
                    ret' <- normalForm (caseTpRet c)
                    branches' <- mapM normalForm (caseBranches c)
                    return $ Case (c { caseArg      = arg',
                                       caseTpRet    = ret',
                                       caseBranches = branches' })
  normalForm t@(Constr ccc x i ps as) =
    do -- traceTCM_ ["Normalizing constr ", show t]
       ps' <- mapM normalForm ps
       as' <- mapM normalForm as
       return $ Constr ccc x i ps' as'
  normalForm t@(Fix a k nm c tp body) =
    do -- traceTCM_ ["Normalizing fix ", show t]
       c' <- normalForm c
       tp' <- normalForm tp
       body' <- pushBind (mkBind nm (mkPi c tp)) $ normalForm body
       return $ Fix a k nm c' tp' body'


-- TODO: check if we need to normalize whSubst
instance NormalForm Branch where
  normalForm (Branch nm cid xs body whSubst) =
    do body' <- normalForm body
       return $ Branch nm cid xs body' whSubst


-- | 'betaRed' bs body args  performs several beta reductions on the term
--   App (Lam bs body) args.
--
--   The number of beta reductions applied is min (length bs, length args)
betaRed :: Context -> Term -> [Term] -> Term
betaRed EmptyCtx body [] = body
betaRed EmptyCtx body args = mkApp body args
betaRed ctx body [] = mkLam ctx body
betaRed (ExtendCtx (Bind _ _ _ Nothing) ctx) body (a:as) = betaRed (subst a ctx) (substN (ctxLen ctx) a body) as
betaRed (ExtendCtx (Bind _ _ _ (Just _)) _) _ _ = __IMPOSSIBLE__


-- | 'iotaRed' @cid@ @args@ @branches@ performs a iota reduction where the
--   argument of the case is a constructor with id @cid@ applied to arguments
--   @args@ (parameters are not needed to perform iota reduction) and @branches@
--   branches of the case
iotaRed :: Int -> [Term] -> [Branch] -> Term
iotaRed cid args branches =
  case find ( (==cid) . brConstrId ) branches of
    Just br -> foldr subst (brBody br) args
    Nothing -> __IMPOSSIBLE__ -- branch

-- | 'muRed' @fix@ @args@ unfolds the fixpoint and applies it to the arguments
--   @args@ shoudl have a length greater or equal than the recursive argument of
--   fix and the recursive argument should be in constructor form
muRed :: Term -> [Term] -> Term
muRed t@(Fix CoI _ _ _ _ body) args = error "Implement nu-red"
muRed t@(Fix I _ _ _ _ body) args = mkApp (subst t body) args
muRed _ _ = __IMPOSSIBLE__


-- Neutral term
-- We assume that all global definitions have been unfolded (see Var case)
-- neutral :: Term -> Bool
-- neutral (Sort _) = False
-- neutral (Pi _ _) = False
-- neutral (Bound _) = True
-- neutral (Var _) = True -- we assume that this Var corresponds to an assumption
-- neutral (Lam _ _) = False
-- neutral (App (Fix CoI n _ _ _ _) ts) = error "Implement neutral CoI"
-- neutral (App (Fix I n _ _ _ _) ts) | length ts < n = False
--                                    | otherwise = neutral $ ts !! (n - 1)
-- neutral (App t _) = neutral t
-- neutral (Constr {}) = False
-- neutral (Fix {}) = False
-- neutral (Case c) = neutral $ caseArg c
-- neutral (Ind {}) = False

