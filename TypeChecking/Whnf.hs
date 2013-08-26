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

module TypeChecking.Whnf(whnF, nF, unfoldPi) where

#include "../undefined.h"
import Utils.Impossible

import Data.List
import qualified Data.Foldable as Fold
import Data.Functor
import Control.Monad.Reader

import Syntax.Common
import Syntax.Internal as I
import Syntax.InternaltoAbstract
import TypeChecking.TCM
import TypeChecking.PrettyTCM

import Utils.Pretty

whnF :: (MonadTCM tcm) => Term -> tcm Term
whnF = whnf

nF :: (MonadTCM tcm) => Term -> tcm Term
nF = normalForm

class Whnf a where
  whnf :: (MonadTCM tcm) => a -> tcm a

instance Whnf a => Whnf (Implicit a) where
  whnf x = do y <- whnf $ implicitValue x
              return $ y <$ x

instance Whnf Term where
  whnf t = metaexp t >>= wH
    where
      wH (App f ts) = do
        w <- wH f
        case w of
          Lam ctx u -> wH $ betaRed ctx u ts
          Fix f
            | length ts < n -> return $ App w ts
            | otherwise ->
              do recArg' <- normalForm recArg
                 case recArg' of
                   Constr {} -> wH (muRed f (first ++ recArg' : last))
                   _ -> return $ App w ts
            where
              n = fixNum f
              (first, recArg, last) = splitRecArg [] (n - 1) ts
              splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
              splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
          _         -> return $ App w ts
      wH t@(Bound k) = do
        len <- localLength
        e <- ask
        when (k >= len) $ traceTCM 1 $ hsep [text "BUG: wH bound ",
                                             int k,
                                             text "in",
                                             prettyPrintTCM e]
        b <- localGet k
        case bindDef b of
          Nothing -> return t
          Just t' -> wH (I.lift (k+1) 0 t')
      wH t@(Var x) =
        do d <- getGlobal x
           case d of
             Definition {} -> whnf (defTerm d)
             Assumption {} -> return t
             _             -> __IMPOSSIBLE__
      wH t@(Case c) =
        do arg' <- wH $ caseArg c
           case arg' of
             Constr _ (_,cid) _ cArgs -> wH $ iotaRed cid cArgs (caseBranches c)
             _ -> case isCofix arg' of
                    Just (_, body, cofix, args) -> wH $ Case (c { caseArg = App (subst cofix body) args })
                    Nothing -> return $ Case (c { caseArg = arg' })
      wH t = return t

-- instance Whnf Bind where
--   whnf (Bind x t) = do w <- whnf t
--                        return $ Bind x w
--   whnf (LocalDef x t u) = do w <- whnf u  -- we only normalize the type
--                              return $ LocalDef x t w


-- isCofix (App (cofix f:T := M) ts) = Just (f, T, M, cofix f := M, ts)
isCofix :: Term -> Maybe (Bind, Term, Term, [Term])
isCofix t@(Fix (FixTerm CoI _ f ctx tp body))          = Just (mkBind f (mkPi ctx tp), body, t, [])
isCofix (App t@(Fix (FixTerm CoI _ f ctx tp body)) ts) = Just (mkBind f (mkPi ctx tp), body, t, ts)
isCofix _                                    = Nothing

unfoldPi :: (MonadTCM tcm) => Type -> tcm (Context, Type)
unfoldPi t =
  do t' <- whnf t
     case t' of
       Pi ctx1 t1 -> do (ctx2, t2) <- pushCtx ctx1 $ unfoldPi t1
                        t2' <- pushCtx (ctx1 +: ctx1) $ whnf t2
                        return (ctx1 +: ctx2, t2')
       _          -> return (ctxEmpty, t')


class NormalForm a where
  normalForm :: (MonadTCM tcm) => a -> tcm a

instance NormalForm a => NormalForm (Maybe a) where
  normalForm Nothing = return Nothing
  normalForm (Just x) = do y <- normalForm x
                           return $ Just y

instance NormalForm a => NormalForm (Implicit a) where
  normalForm x = do y <- normalForm (implicitValue x)
                    return $ y <$ x

instance NormalForm Bind where
  normalForm b =
    do t <- normalForm (bindType b)
       u <- normalForm (bindDef b)
       return $ b { bindType = t, bindDef = u }


instance NormalForm Context where
  normalForm CtxEmpty = return CtxEmpty
  normalForm (CtxExtend x xs) = do x' <- normalForm x
                                   xs' <- pushBind x' $ normalForm xs
                                   return $ CtxExtend x' xs'


instance NormalForm Term where
  normalForm x = metaexp x >>= nF
    where
      nF :: (MonadTCM tcm) => Term -> tcm Term
      nF t@(Sort s) = return t
      nF (Pi c t) = liftM2 Pi (normalForm c) (pushCtx c $ nF t)
      nF t@(Bound k) = do
        e <- ask
        when (k >= envLen e) $ error $ "normalform out of bound: " ++ show k ++ "  " ++ show e
        case bindDef (envGet e k) of
          Nothing -> return t
          Just t' -> nF (I.lift (k+1) 0 t')
      nF t@(Meta k) = do
        (Just g) <- getGoal k
        case goalTerm g of
          Nothing -> return t
          Just x  -> nF x
      nF t@(Var x) = do
        traceTCM 30 $ hsep [text "Normalizing Var ", prettyPrintTCM x]
        u <- getGlobal x
        case u of
          Definition {} -> do
            traceTCM 30 $ hsep [text "global", prettyPrintTCM (defTerm u)]
            nF (defTerm u)
          Assumption _    -> return t
          _               -> __IMPOSSIBLE__
      nF (Lam c t) = liftM2 Lam (normalForm c) (pushCtx c $ nF t)
      nF t@(App t1 ts) = do
        traceTCM 30 $ vcat [ text "Normalizing in ", ask >>= prettyPrintTCM
                           , text "APP :" <+> prettyPrintTCM t]
        t1' <- whnf t1
        case t1' of
          Lam ctx u  ->
            do traceTCM 30 $ (hsep [text "Beta Reduction on ",
                                    prettyPrintTCM t1',
                                    text " and ",
                                    prettyPrintTCM ts]
                              $$ hsep [text "reduces to ", prettyPrintTCM (betaRed ctx u ts)])
               nF $ betaRed ctx u ts
          App u1 us -> do ts' <- mapM nF ts
                          us' <- mapM nF us
                          return $ mkApp u1 (us' ++ ts')
          Fix (f@(FixTerm I n _ _ _ _))
            | length ts < n -> do -- traceTCM_ ["Fix without enough args ", show (length ts), " < ", show n]
                                  ts' <- mapM nF ts
                                  return $ App t1' ts'
            | otherwise ->
              do -- traceTCM_ ["Fix enough args\nFirst ", show first, "\nRec ", show recArg, "\nLast ", show last]
                 recArg' <- nF recArg
                 case recArg' of
                   Constr {} ->
                             do -- traceTCM_ ["Mu Reduction ",
                                --            show t1', "\non\n",
                                --            show (first ++ recArg' : last)]
                                nF (muRed f (first ++ recArg' : last))
                   _    -> do -- traceTCM_ ["No recursion arg = ", show recArg']
                              first' <- mapM nF first
                              last'  <- mapM nF last
                              return $ mkApp t1' (first' ++ recArg' : last')
            where (first, recArg, last) = splitRecArg [] (n - 1) ts
                  splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                  splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
          _         -> do -- traceTCM_ ["Not handled application", show t1']
                          ts' <- mapM nF ts
                          return $ mkApp t1' ts'
      nF t@(Ind _ _) = do
        traceTCM 80 $ hsep [text "Normalizing Ind ", prettyPrintTCM t]
        return t
      nF t@(Case c) =
        do traceTCM 30 $ (hsep [text "Normalizing Case in ", prettyPrintTCM t]
                          $$ hsep [text "arg ", prettyPrintTCM (caseArg c)])
           arg' <- nF $ caseArg c
           case arg' of
             Constr _ (_,cid) _ cArgs ->
                         do -- traceTCM_ ["Iota Reduction ",
                            --            show cid, " ", show cArgs,
                            --            "\nwith branches\n",
                            --           show (caseBranches c)]
                            nF $ iotaRed cid cArgs (caseBranches c)
             _ -> case isCofix arg' of
                    Just (bind, body, cofix, args) ->
                      do
                        traceTCM 30 $ vcat [text "normal form case " <> prettyPrintTCM t,
                                            text "body " <> pushBind bind (prettyPrintTCM body),
                                            text "cofix " <> prettyPrintTCM cofix,
                                            text "args " <> prettyPrintTCM args]
                        nF $ Case (c { caseArg = App (subst cofix body) args })
                    Nothing ->
                      do -- traceTCM_ ["Case in normal form ", show t]
                        ret' <- nF (caseTpRet c)
                        branches' <- mapM normalForm (caseBranches c)
                        return $ Case (c { caseArg      = arg',
                                           caseTpRet    = ret',
                                           caseBranches = branches' })
      nF t@(Constr x i ps as) =
        do -- traceTCM_ ["Normalizing constr ", show t]
           ps' <- mapM nF ps
           as' <- mapM nF as
           return $ Constr x i ps' as'
      nF t@(Fix f) = liftM Fix (normalForm f)


instance NormalForm FixTerm where
  normalForm (FixTerm a k nm c tp body) =
    liftM3 (FixTerm a k nm) (normalForm c) (nF tp)
    (pushBind (mkBind nm (mkPi c tp)) $ nF body)


-- TODO: check if we need to normalize whSubst
instance NormalForm Branch where
  normalForm (Branch nm cid xs body whSubst) =
    do body' <- normalForm body
       return $ Branch nm cid xs body' whSubst


-- | 'betaRed' ctx body args  performs several beta reductions on the term
--   App (Lam ctx body) args.
--
--   The number of beta reductions applied is min (length ctx, length args)
betaRed :: Context -> Term -> [Term] -> Term
betaRed CtxEmpty body args = mkApp body args
betaRed ctx body [] = mkLam ctx body
betaRed (CtxExtend b bs) body (a:as) =
  betaRed (subst a bs) (substN (ctxLen bs) a body) as
-- betaRed (Consctx (Bind _ _ _ (Just _)) _) _ _ = __IMPOSSIBLE__


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
muRed :: FixTerm -> [Term] -> Term
-- muRed t@(Fix CoI _ _ _ _ body) args = error "Implement nu-red"
muRed f args = mkApp (subst (Fix f) (fixBody f)) args
-- muRed _ _ = __IMPOSSIBLE__




class MetaExp a where
  metaexp :: (MonadTCM tcm) => a -> tcm a

instance MetaExp a => MetaExp (Maybe a) where
  metaexp Nothing = return Nothing
  metaexp (Just x) = liftM Just (metaexp x)

instance MetaExp Term where
  metaexp (Pi ctx t) = do ctx' <- metaexp ctx
                          t' <- metaexp t
                          return $ Pi ctx' t'
  metaexp (Lam ctx t) = do ctx' <- metaexp ctx
                           t' <- metaexp t
                           return $ Lam ctx' t'
  metaexp (App f ts) = do f' <- metaexp f
                          ts' <- mapM metaexp ts
                          return $ App f' ts'
  metaexp t@(Meta k) = do (Just g) <- getGoal k
                          case goalTerm g of
                            Nothing -> return t
                            Just x -> metaexp x
  metaexp (Constr nmC nmI pars args) =
    liftM2 (Constr nmC nmI) (mapM metaexp pars) (mapM metaexp args)
  metaexp (Fix f) = liftM Fix (metaexp f)
  metaexp t@(Case c) = liftM Case (metaexp c)
  metaexp t = return t -- Sort, Bound, Var, Ind

instance MetaExp FixTerm where
  metaexp (FixTerm k n nm ctx tp body) =
    do
      ctx'  <- metaexp ctx
      tp'   <- metaexp tp
      body' <- metaexp body
      return $ FixTerm k n nm ctx' tp' body'



instance MetaExp Context where
  metaexp CtxEmpty = return CtxEmpty
  metaexp (CtxExtend b bs) = do t <- metaexp (bindType b)
                                let b' = b { bindType = t }
                                bs' <- metaexp bs
                                return $ CtxExtend b' bs'


instance MetaExp CaseTerm where
  metaexp c = do
    arg' <- metaexp (caseArg c)
    in'  <- metaexp (caseIn c)
    tp'  <- metaexp (caseTpRet c)
    br'  <- mapM metaexp (caseBranches c)
    let c' = c { caseArg = arg'
               , caseIn  = in'
               , caseTpRet = tp'
               , caseBranches = br' }
    return c'

instance MetaExp CaseIn where
  metaexp i = do
    in'   <- metaexp (inBind i)
    args' <- mapM metaexp (inArgs i)
    let i' = i { inBind = in'
               , inArgs = args' }
    return i'

instance MetaExp Branch where
  metaexp b = do
    body' <- metaexp (brBody b)
    subst' <- metaexp (brSubst b)
    let b' = b { brBody = body'
               , brSubst = subst' }
    return b'

instance MetaExp Subst where
  metaexp (Subst sg) = do sg' <- mapM metaSubst sg
                          return $ Subst sg'
    where
      metaSubst (x, t) = do t' <- metaexp t
                            return (x, t')

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

