{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
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

{-# LANGUAGE CPP    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CICwf.TypeChecking.Whnf where

#include "undefined.h"
import           CICwf.Utils.Impossible

import           Control.Monad.Reader

import           Data.Functor
import           Data.List
import           Data.Monoid
import qualified Data.Traversable       as Tr

import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal        as I
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.PrettyTCM hiding ((<>))
-- import qualified CICwf.TypeChecking.PrettyTCM as PP ((<>))
import           CICwf.TypeChecking.TCM

import           CICwf.Utils.Sized


data WValue = WLam Context Term
            | WPi Context Term
            | WSort Sort
            | WBound Int
            | WCBound Int Annot
            | WVar Name
            | WCVar Name Annot
            | WSIdent Name Annot
            | WConstr Name (Name, Int) [Term] [Term]
            | WBlockedFix FixTerm Annot
            | WInd Annot Bool Name [Term]
            | WSubset SizeName Annot Type
            | WIntro Annot Term
            | WCoIntro SizeName Annot Term
            deriving(Show)

data Frame = FApp [I.Term]
           | FCase CaseTerm -- arg is Prop
           | FIntro Annot
           | FCoIntro SizeName Annot
           deriving(Show)

instance PrettyTCM Frame where
  prettyTCM (FApp ts) = text "FApp" <+> prettyTCM ts
  prettyTCM (FCase c) = text "FCase" <+> prettyTCM (Case c)
  prettyTCM (FIntro a) = text "FIntro" <+> prettyTCM a
  prettyTCM (FCoIntro im a) = text "FCoIntro" <+> prettyTCM im <+> text "⊑" <+> prettyTCM a

instance PrettyTCM Stack where
  prettyTCM EnvEmpty = empty
  prettyTCM (s :< f) = prettyTCM s $$ text "⊳" <+> prettyTCM f

type Stack = Env Frame

data WCaseTerm = WCaseTerm I.Type [I.Branch]
               deriving(Show)

stackToTerm :: Stack -> WValue -> Term
stackToTerm s w = unravel s (wvalueToTerm w)
  where
    unravel EnvEmpty t = t
    unravel (s :< f) t = unravel s (frameToTerm f t)


wvalueToTerm :: WValue -> Term
wvalueToTerm (WLam ctx t) = mkLam ctx t
wvalueToTerm (WPi ctx t) = mkPi ctx t
wvalueToTerm (WSort s) = Sort s
wvalueToTerm (WBound n) = Bound n
wvalueToTerm (WCBound n a) = CBound n a
wvalueToTerm (WVar x) = Var x
wvalueToTerm (WSIdent x a) = SIdent x a
wvalueToTerm (WConstr nm cid pars args) = mkApp (Constr nm cid pars) args
wvalueToTerm (WBlockedFix f a) = Fix f True a
wvalueToTerm (WInd a b x ps) = Ind a b x ps
wvalueToTerm (WSubset im a t) = Subset im a t
wvalueToTerm (WIntro a t) = Intro a t
wvalueToTerm (WCoIntro im a t) = CoIntro im a t

frameToTerm :: Frame -> Term -> Term
frameToTerm (FApp args) t = mkApp t args
frameToTerm (FCase c) t = Case (c { caseArg = t })
frameToTerm (FIntro a) t = Intro a t
frameToTerm (FCoIntro im a) t = CoIntro im a t

scat :: Stack -> Stack -> Stack
scat s1 EnvEmpty = s1
scat (s1 :< FApp ts) (EnvEmpty :< FApp ts') = s1 :< FApp (ts ++ ts')
scat s1 (s2 :< f) = scat s1 s2 :< f


-- Call-by-name
wHnf :: (MonadTCM tcm) => Stack -> Term -> tcm (Stack, WValue)
wHnf s t = do
  traceTCM 45 $ text "-------" $$ text "whnf" <+> prettyTCM s $$ nest 2 (text ">>" <+> prettyTCM t)
  wH s t

wH :: (MonadTCM tcm) => Stack -> Term -> tcm (Stack, WValue)
wH k (Sort s) = return (k, WSort s)
wH k (Pi ctx t) = return (k, WPi ctx t)
wH k (Bound n) = do-- return (k, WBound n)
  b <- localGet n
  case bindDef b of
    Nothing -> return (k, WBound n)
    Just t' -> wH k (I.lift (n+1) 0 t')
wH k (CBound n a) = return (k, WCBound n a)
wH k (Var x) = do
  d <- getGlobal x
  case d of
    Definition {} -> wHnf k (defTerm d)
    Assumption {} -> return (k, WVar x)
    _ -> __IMPOSSIBLE__
wH k (CVar x a) = do
  d <- getGlobal x
  case d of
    Cofixpoint {} -> wHnf k (Fix (cofixTerm d) False a)
    Assumption {} -> return (k, WCVar x a)
    _ -> __IMPOSSIBLE__
wH k (SIdent x a) = return (k, WSIdent x a)
wH k (Lam ctx t) = hReduce k (WLam ctx t)
wH k (App t ts) = wHnf (k :< FApp ts) t
-- wH k (Meta _) =
wH k (Constr nm cid ps) = hReduce k (WConstr nm cid ps [])
wH k t@(Fix f blocked a)
  | blocked && isInfty a = wHnf k (subst (Fix f True Empty) (mkLam (fixArgs f) (fixBody f))) -- TODO: this is a bug; this case should not happen
  | blocked = return (k, WBlockedFix f a)
  | otherwise = wHnf k (subst (Fix f True Empty) (mkLam (fixArgs f) (fixBody f)))
wH k (Case c) = wHnf (k :< FCase (c { caseArg = (Sort Prop) })) (caseArg c)
wH k (Ind a b x pars) = return (k, WInd a b x pars)
wH k (Intro a t) = wHnf (k :< FIntro a) t
wH k (CoIntro im a t) = wHnf (k :< FCoIntro im a) t
wH k (Subset im a t) = return (k, WSubset im a t)

hReduce :: (MonadTCM tcm) => Stack -> WValue -> tcm (Stack, WValue)
hReduce s w = do
  traceTCM 45 $ text "=====" $$ text "hReduce" <+> prettyTCM s $$ nest 2 (text "<<" <+> text (show w))
  headRed s w

headRed :: (MonadTCM tcm) => Stack -> WValue -> tcm (Stack, WValue)
headRed (st :< FApp ts) (WLam ctx b) = wHnf st (betaRed ctx b ts)
headRed (st :< FApp ts2) (WConstr nm cid ps ts1) =
  headRed st (WConstr nm cid ps (ts1 ++ ts2))
headRed (st :< FIntro a) t@(WConstr {}) =
  headRed st (WIntro a (wvalueToTerm t))
headRed (st :< FCoIntro im a) t@(WConstr {}) =
  headRed st (WCoIntro im a (wvalueToTerm t))
headRed (st :< FCase c) (WIntro a (Constr nm cid ps)) =
  wHnf st (iotaRed a (snd cid) [] (caseBranches c))
headRed (st :< FCase c) (WIntro a (App (Constr nm cid ps) args)) =
  wHnf st (iotaRed a (snd cid) args (caseBranches c))
headRed (st :< FCase c) (WCoIntro im a (Constr nm cid ps)) =
  wHnf st (coiotaRed (snd cid) [] (caseBranches c))
headRed (st :< FCase c) (WCoIntro im a (App (Constr nm cid ps) args)) =
  wHnf st (coiotaRed (snd cid) (substSizeName im (getCocaseSize c) args) (caseBranches c))
headRed EnvEmpty w = return (EnvEmpty, w)
headRed st w = traceTCM 1 (text "=====" $$ text "hReduce" <+> prettyTCM st $$ nest 2 (text "<<" <+> text (show w))) >> typeError noRange (GenericError "HEADRED")


whnf :: (MonadTCM tcm) => Term -> tcm Term
whnf t = do
  (s, w) <- wHnf EnvEmpty t
  return (stackToTerm s w)

nF :: (MonadTCM tcm) => Term -> tcm Term
nF = normalForm


-- isCofix (App (Fix f...) ts) | fixKind f == CoI = Just (Fix f..., ts)
-- isCofix :: Term -> Maybe (FixTerm, [Term], Annot)
-- isCofix (SizeApp (Fix f) s)          | fixKind f == CoI = Just (f, [], s)
-- isCofix (SizeApp (App (Fix f) ts) s) | fixKind f == CoI = Just (f, ts, s)
-- isCofix _                                   = Nothing

-- -- isCofix (App (cofix f:T := M) ts) = Just (f, T, M, cofix f := M, ts)
-- isCofix :: Term -> Maybe (Bind, Term, Term, [Term])
-- isCofix t@(Fix (FixTerm CoI _ f stage ctx tp body))    = Just (mkBind f (mkPi ctx tp), body, t, [])
-- isCofix (App t@(Fix (FixTerm CoI _ f stage ctx tp body)) ts) = Just (mkBind f (mkPi ctx tp), body, t, ts)
-- isCofix _                                    = Nothing

unfoldPi :: (MonadTCM tcm) => Type -> tcm (Context, Type)
unfoldPi t =
  do t' <- whnf t
     case t' of
       Pi ctx1 t1 -> do (ctx2, t2) <- pushCtx ctx1 $ unfoldPi t1
                        t2' <- pushCtx (ctx1 <> ctx1) $ whnf t2
                        return (ctx1 <> ctx2, t2')
       _          -> return (ctxEmpty, t')


class NormalForm a where
  normalForm :: (MonadTCM tcm) => a -> tcm a


instance NormalForm a => NormalForm (Maybe a) where
  normalForm = Tr.mapM normalForm


instance NormalForm a => NormalForm (Named a) where
  normalForm = Tr.mapM normalForm


instance NormalForm a => NormalForm [a] where
  normalForm = Tr.mapM normalForm




instance NormalForm a => NormalForm (Implicit a) where
  normalForm x = do y <- normalForm (implicitValue x)
                    return $ y <$ x


instance NormalForm Sort where
  normalForm = return

instance NormalForm a => NormalForm (Arg a) where
  normalForm = Tr.mapM normalForm

instance NormalForm Bind where
  normalForm b = do
    t <- normalForm (bindType b)
    u <- normalForm (bindDef b)
    return $ b { bindType = t, bindDef = u }



instance NormalForm Context where
  normalForm CtxEmpty = return CtxEmpty
  normalForm (x :> xs) = do x' <- normalForm x
                            xs' <- pushBind x' $ normalForm xs
                            return $ x' :> xs'


instance NormalForm WValue where
  normalForm (WLam ctx t) = do
    ctx' <- normalForm ctx
    t' <- pushCtx ctx' $ normalForm t
    return $ WLam ctx' t'
  normalForm (WPi ctx t) = do
    ctx' <- normalForm ctx
    t' <- pushCtx ctx' $ normalForm t
    return $ WPi ctx' t'
  normalForm w@(WSort {}) = return w
  normalForm w@(WBound {}) = return w
  normalForm w@(WCBound {}) = return w
  normalForm w@(WVar {}) = return w
  normalForm w@(WCVar {}) = return w
  normalForm w@(WSIdent {}) = return w
  normalForm (WConstr nm cid pars args) = do
    pars' <- normalForm pars
    args' <- normalForm args
    return (WConstr nm cid pars' args')
  normalForm (WBlockedFix f a) = do
    f' <- normalForm f
    return (WBlockedFix f' a)
  normalForm (WInd a b x pars) = WInd a b x <$> normalForm pars
  normalForm (WSubset im a t) = WSubset im a <$> normalForm t
  normalForm (WIntro a t) = WIntro a <$> normalForm t
  normalForm (WCoIntro im a t) = WCoIntro im a <$> normalForm t


instance NormalForm Term where
  normalForm t = do
    traceTCM 40 $ text "*******" $$ text "in context" $$ (ask >>= prettyTCM) $$ text "Normalform:" <+> prettyTCM t
    t' <- normalForm' t
    traceTCM 40 $ text "*******" $$ text "Got:" <+> prettyTCM t'
    return t'
    where
      normalForm' :: (MonadTCM tcm) => Term -> tcm Term
      normalForm' t = do
        -- traceTCM 40 $ text "*******" $$ text "Normalform:" <+> prettyTCM t
        (s, w) <- wHnf EnvEmpty t
        -- traceTCM 40 $ text "*******" $$ text "Got:" <+> prettyTCM (stackToTerm s w)
        w' <- normalForm w
        nF s (wvalueToTerm w')
        where
          nF :: (MonadTCM tcm) => Stack -> Term -> tcm Term
          nF EnvEmpty t = return t
          nF (s :< FApp args) t = do
            args' <- mapM normalForm' args
            nF s (mkApp t args')
          nF (s :< FCase c) t = do
            ret' <- normalForm' (caseTpRet c)
            branches' <- mapM normalForm (caseBranches c)
            in' <- normalForm (caseIndices c)
            nF s (Case (c { caseArg      = t
                          , caseTpRet    = ret'
                          , caseIndices  = in'
                          , caseBranches = branches'
                          }))
          nF (s :< FIntro a) t = nF s (Intro a t)
          nF (s :< FCoIntro im a) t = nF s (CoIntro im a t)


instance NormalForm FixTerm where
  normalForm (FixTerm a k nm stage c tp body) =
    liftM3 (FixTerm a k nm stage) (normalForm c)
    (pushCtx c $ normalForm tp)
    (pushCtx c $ pushBind (mkBind nm (mkPi c tp)) $ nF body)


-- instance (NormalForm a, Tr.Traversable t) => NormalForm (t a) where
--   normalForm = Tr.mapM normalForm

-- instance NormalForm

instance NormalForm IndicesSpec where
  normalForm = fmap IndicesSpec . normalForm . indspecArgs

instance NormalForm SinglePattern where
  normalForm (PatternDef x t) = fmap (PatternDef x) (normalForm t)
  normalForm t = return t




-- TODO: do we need to fix this fake types?
instance NormalForm Branch where
  normalForm (Branch sv nm cid args body) = do
    body' <- pushCtx (patternCtx args) $ normalForm body
    return $ Branch sv nm cid args body'
      where
        fakeTypedPattern (PatternVar x)   = mkBind x (Sort Prop)
        fakeTypedPattern (PatternDef x t) = mkBindDef x (Sort Prop) t
        patternCtx = foldr ((:>) . fakeTypedPattern) CtxEmpty


-- | 'betaRed' ctx body args  performs several beta reductions on the term
--   App (Lam ctx body) args.
--
--   The number of beta reductions applied is min (length ctx, length args)
-- betaRed :: Context -> Term -> [Term] -> Term
-- betaRed CtxEmpty body args = mkApp body args
-- betaRed ctx body [] = mkLam ctx body
-- betaRed (b :> bs) body (a:as) =
--   betaRed (subst a bs) (substN (ctxLen bs) a body) as
betaRed :: Context -> Term -> [Term] -> Term
betaRed ctx body args = mkApp (substList0 args0 (mkLam ctx1 body)) args1
  where
    n              = size ctx `min` size args
    (_, ctx1)   = ctxSplitAt n ctx
    (args0, args1) = splitAt n args



-- | 'iotaRed' @cid@ @args@ @branches@ performs a iota reduction where the
--   argument of the case is a constructor with id @cid@ applied to arguments
--   @args@ (parameters are not needed to perform iota reduction) and @branches@
--   branches of the case
iotaRed :: Annot -> Int -> [Term] -> [Branch] -> Term
iotaRed annot cid args branches =
  case find ( (==cid) . brConstrId ) branches of
    Just br ->
      case brSize br of
        Just km -> substList0 args (substSizeName km annot (unblock km (brBody br)))
        Nothing -> __IMPOSSIBLE__
    Nothing -> __IMPOSSIBLE__ -- branch

coiotaRed :: Int -> [Term] -> [Branch] -> Term
coiotaRed cid args branches =
  case find ( (==cid) . brConstrId ) branches of
    Just br ->
      case brSize br of
        Just km -> __IMPOSSIBLE__
        Nothing -> substList0 args (brBody br)
    Nothing -> __IMPOSSIBLE__ -- branch

-- | 'muRed' @fix@ @args@ unfolds the fixpoint and applies it to the arguments
--   @args@ shoudl have a length greater or equal than the recursive argument of
--   fix and the recursive argument should be in constructor form
-- muRed :: FixTerm -> [Term] -> Term
-- -- muRed t@(Fix CoI _ _ _ _ body) args = error "Implement nu-red"
-- muRed f args = mkApp (subst (Fix f) (mkLam (fixArgs f) (fixBody f))) args
-- -- muRed _ _ = __IMPOSSIBLE__

-- muRed :: FixTerm -> Annot -> [Term] -> Term
-- muRed f s args =
--   betaRed (mkBind (fixName f) (Sort Prop) :> fixArgs f) (substSizeName (getFixStage f) s (fixBody f)) (Fix f : args)


extractConstr :: Term -> Maybe (Annot, Term, [Term])
extractConstr (Intro im t) =
  case unApp t of
    (c@Constr {}, args) -> Just (im, c, args)
    _ -> Nothing
extractConstr _ = Nothing

extractCoconstr :: Term -> Maybe (SizeName, Term, [Term])
extractCoconstr (CoIntro im a t) =
  case unApp t of
    (c@Constr {}, args) -> Just (im, c, args)
    _ -> Nothing
extractCoconstr _ = Nothing
