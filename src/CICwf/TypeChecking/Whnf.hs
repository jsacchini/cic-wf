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

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CICwf.TypeChecking.Whnf where

import           CICwf.Utils.Impossible

import           Control.Monad.Reader

import           Data.Functor
import           Data.List
import           Data.Monoid
import qualified Data.Traversable       as Tr

import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal        as I

import           CICwf.TypeChecking.PrettyTCM hiding ((<>))
import qualified CICwf.TypeChecking.PrettyTCM as PP ((<>))
import           CICwf.TypeChecking.TCM

import           CICwf.Utils.Sized


nF :: (MonadTCM tcm) => Term -> tcm Term
nF = normalForm

class Whnf a where
  whnf :: (MonadTCM tcm) => a -> tcm a

instance Whnf a => Whnf (Implicit a) where
  whnf x = do y <- whnf $ implicitValue x
              return $ y <$ x

instance Whnf Term where
  whnf = wH -- metaexp t >>= wH
    where
      wH (App f ts) = do
        w <- wH f
        case w of
          Lam ctx u -> wH $ betaRed ctx u ts
          SizeApp (Fix f) s
            | length ts <= n -> return $ mkApp w ts
            | otherwise -> do
              recArg' <- normalForm recArg
              case recArg' of
                Constr {} -> do
                  traceTCM 70 $ vcat [ text "Mu Reduction"
                                     , prettyTCM w
                                     , text "on"
                                     , prettyTCM (fs ++ recArg' : ls)
                                     , text "RESULT"
                                     , prettyTCM (muRed f s (fs ++ recArg' : ls)) ]
                  wH (muRed f s (fs ++ recArg' : ls))
                App (Constr {}) _ -> do
                  traceTCM 70 $ vcat [ text "Mu Reduction"
                                     , prettyTCM w
                                     , text "on"
                                     , prettyTCM (fs ++ recArg' : ls)
                                     , text "RESULT"
                                     , prettyTCM (muRed f s (fs ++ recArg' : ls)) ]
                  wH (muRed f s (fs ++ recArg' : ls))
                _ -> return $ App w ts
            where
              n = fixNum f
              (fs, recArg : ls) = splitAt n ts
              -- (first, recArg, last) = splitRecArg [] n ts
              -- splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
              -- splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
          _         -> return $ App w ts
      wH t@(Bound k) = do
        len <- localLength
        e <- ask
        when (k >= len) $ traceTCM 1 $ hsep [text "BUG: wH bound ",
                                             int k,
                                             text "in",
                                             prettyTCM e]
        b <- localGet k
        case bindDef b of
          Nothing -> return t
          Just t' -> wH (I.lift (k+1) 0 t')
      wH t@(Var x) =
        do d <- getGlobal x
           case d of
             Definition {} -> whnf (defTerm d)
             Assumption {} -> return t
             Cofixpoint {} -> whnf (Fix (cofixTerm d))
             _             -> __IMPOSSIBLE__
      wH t@(Case c) | isCocase c =
        do arg' <- wH $ caseArg c
           case extractCoconstr arg' of
             Just (im, Constr _ (_,cid) _, cArgs) ->
               wH $ coiotaRed cid (substSizeName im (getCocaseSize c) cArgs)
                              (caseBranches c)
             _ -> case isCofix arg' of
                    Just (cofix, args, s) -> wH $ Case (c { caseArg = muRed cofix s args })
                    Nothing -> return $ Case (c { caseArg = arg' })
                    | otherwise =
        do arg' <- wH $ caseArg c
           case extractConstr arg' of
             Just (s, Constr _ (_,cid) _, cArgs) ->
               wH $ iotaRed s cid cArgs (caseBranches c)
             _ -> return $ Case (c { caseArg = arg' })

      wH (Intro s t) = Intro s <$> wH t
      wH (CoIntro s t) = CoIntro s <$> wH t
      wH (SizeApp t s) = flip SizeApp s <$> wH t
      wH t = return t

-- instance Whnf Bind where
--   whnf (Bind x t) = do w <- whnf t
--                        return $ Bind x w
--   whnf (LocalDef x t u) = do w <- whnf u  -- we only normalize the type
--                              return $ LocalDef x t w


-- isCofix (App (Fix f...) ts) | fixKind f == CoI = Just (Fix f..., ts)
isCofix :: Term -> Maybe (FixTerm, [Term], Annot)
isCofix (SizeApp (Fix f) s)          | fixKind f == CoI = Just (f, [], s)
isCofix (SizeApp (App (Fix f) ts) s) | fixKind f == CoI = Just (f, ts, s)
isCofix _                                   = Nothing

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


instance NormalForm Term where
  normalForm = nF -- metaexp x >>= nF
    where
      nF :: (MonadTCM tcm) => Term -> tcm Term
      nF t@(Sort s) = return t
      nF (Pi c t) = liftM2 Pi (normalForm c) (pushCtx c $ nF t)
      nF t@(Bound k) = do
        e <- ask
        traceTCM 70 $ hsep [ text "normal form bound"
                           , prettyTCM k
                           , text "in ctx"
                           , ask >>= prettyTCM ]
        when (k >= envLen e) $ error $ "normalform out of bound: " ++ show k -- ++ "  " ++ show e
        case bindDef (envGet e k) of
          Nothing -> return t
          Just t' -> nF (I.lift (k+1) 0 t')
      nF t@(Meta k) = do
        (Just g) <- getGoal k
        case goalTerm g of
          Nothing -> return t
          Just x  -> nF x
      nF t@(Var x) = do
        traceTCM 70 $ hsep [text "Normalizing Var ", prettyTCM x]
        u <- getGlobal x
        case u of
          Definition {} -> do
            traceTCM 70 $ hsep [text "global", prettyTCM (defTerm u)]
            nF (defTerm u)
          Assumption _    -> return t
          Cofixpoint {} -> do
            traceTCM 70 $ hsep [text "NF cofixpoint", prettyTCM (Fix (cofixTerm u))]
            nF (Fix (cofixTerm u))
          _               -> __IMPOSSIBLE__
      nF (Lam c t) = liftM2 Lam (normalForm c) (pushCtx c $ nF t)
      nF t@(App _ _) = do
        let (t1, ts) = unApp t
        traceTCM 70 $ vcat [ text "Normalizing in ", ask >>= prettyTCM
                           , text "APP :" <+> prettyTCM t]
        t1' <- whnf t1
        case t1' of
          Lam ctx u  ->
            do traceTCM 70 $ (hsep [text "Beta Reduction on ",
                                    prettyTCM t1',
                                    text " and ",
                                    prettyTCM ts]
                              $$ hsep [text "reduces to ", prettyTCM (betaRed ctx u ts)])
               nF $ betaRed ctx u ts
          App u1 us -> do ts' <- mapM nF ts
                          us' <- mapM nF us
                          return $ mkApp u1 (us' ++ ts')
          SizeApp (Fix (f@(FixTerm I n _ _ _ _ _))) s
            | length ts <= n -> do -- traceTCM_ ["Fix without enough args ", show (length ts), " < ", show n]
                                  ts' <- mapM nF ts
                                  return $ App t1' ts'
            | otherwise -> do
                 let (_, recArg : _) = splitAt n ts
                 traceTCM 70 $ vcat [ text "Fix enough args. rec arg "
                                    , prettyTCM recArg ]
                 recArg' <- nF recArg
                 case recArg' of
                   (Intro _ (Constr {})) -> do
                     traceTCM 70 $ vcat [ text "Mu Reduction"
                                        , prettyTCM t1'
                                        , text "on"
                                        , prettyTCM (fs ++ recArg' : ls)
                                        , text "RESULT"
                                        , prettyTCM (muRed f s (fs ++ recArg' : ls)) ]
                     nF (muRed f s (fs ++ recArg' : ls))
                   (Intro _ (App (Constr {}) _)) -> do
                     traceTCM 70 $ vcat [ text "Mu Reduction"
                                        , prettyTCM t1'
                                        , text "on"
                                        , prettyTCM (fs ++ recArg' : ls)
                                        , text "RESULT"
                                        , prettyTCM (muRed f s (fs ++ recArg' : ls)) ]
                     nF (muRed f s (fs ++ recArg' : ls))
                   _    -> do
                     traceTCM 70 $ hsep [text "No recursion arg = ", text (show recArg')]
                     fs' <- mapM nF fs
                     ls'  <- mapM nF ls
                     return $ mkApp t1' (fs' ++ recArg' : ls')
            where (fs, recArg : ls) = splitAt n ts
                  -- splitRecArg xs 0 (r : rs) = (reverse xs, r, rs)
                  -- splitRecArg xs k (r : rs) = splitRecArg (r : xs) (k-1) rs
          _         -> do traceTCM 80 $ hsep [ text "Not handled application", prettyTCM t1']
                          ts' <- mapM nF ts
                          return $ mkApp t1' ts'
      nF t@(Ind a b x ps) =
        do
          traceTCM 80 $ hsep [text "Normalizing Ind ", prettyTCM t]
          liftM (Ind a b x) (mapM nF ps)
      nF t@(Case c) | isCocase c =
        do traceTCM 70 $ (hsep [text "Normalizing Case in ", prettyTCM t]
                          $$ hsep [text "arg ", prettyTCM (caseArg c)])
           arg' <- nF $ caseArg c
           case extractCoconstr arg' of
             Just (im, Constr _ (_,cid) cPars, cArgs) -> do
                   traceTCM 70 $ vcat [ text "Iota Reduction "
                                      , prettyTCM cid
                                      , prettyTCM cArgs
                                      , text "RESULT"
                                      , prettyTCM (coiotaRed cid (substSizeName im (getCocaseSize c) cArgs) (caseBranches c))
                                      ]
                   nF $ coiotaRed cid (substSizeName im (getCocaseSize c) cArgs)
                                  (caseBranches c)
             Nothing ->
                  case isCofix arg' of
                    Just (cofix, args, s) -> do
                      traceTCM 70 $ vcat [text "normal form case " PP.<> prettyTCM t,
                                          text "cofix " PP.<> prettyTCM cofix,
                                          text "args " PP.<> prettyTCM args]
                      nF $ Case (c { caseArg = muRed cofix s args })
                    Nothing -> do
                      traceTCM 70 $ text "Case in normal form " <+> prettyTCM t
                      traceTCM 70 $ text "Normalizing RET " <+> prettyTCM (caseTpRet c)
                      ret' <- nF (caseTpRet c)
                      traceTCM 70 $ text "Normalizing branches "
                      branches' <- mapM normalForm (caseBranches c)
                      in' <- normalForm (caseIndices c)
                      return $ Case (c { caseArg      = arg'
                                       , caseTpRet    = ret'
                                       , caseIndices  = in'
                                       , caseBranches = branches'
                                       })
                    | otherwise =
        do traceTCM 70 $ (hsep [text "Normalizing Case in ", prettyTCM t]
                          $$ hsep [text "arg ", prettyTCM (caseArg c)])
           arg' <- nF $ caseArg c
           case extractConstr arg' of
             Just (s, Constr _ (_,cid) cPars, cArgs) -> do
               traceTCM 70 $ vcat [ text "Iota Reduction "
                                  , prettyTCM cid
                                  , prettyTCM cArgs
                                  , text "RESULT"
                                  , prettyTCM (iotaRed s cid cArgs (caseBranches c))
                                  ]
               nF $ iotaRed s cid cArgs (caseBranches c)
             Nothing -> do
               traceTCM 70 $ text "Case in normal form " <+> prettyTCM t
               traceTCM 70 $ text "Normalizing RET " <+> prettyTCM (caseTpRet c)
               ret' <- nF (caseTpRet c)
               traceTCM 70 $ text "Normalizing branches "
               branches' <- mapM normalForm (caseBranches c)
               in' <- normalForm (caseIndices c)
               return $ Case (c { caseArg      = arg'
                                , caseTpRet    = ret'
                                , caseIndices  = in'
                                , caseBranches = branches'
                                })

      nF t@(Constr x i ps) =
        do -- traceTCM_ ["Normalizing constr ", show t]
           ps' <- mapM nF ps
           return $ Constr x i ps'
      nF t@(Fix f) = do
        ctxn <- normalForm $ fixArgs f
        tpn  <- pushCtx ctxn $ normalForm (fixType f)
        let recf = mkBind (fixName f) (mkPi ctxn tpn)
        bodyn <- pushBind recf $ pushCtx ctxn $ normalForm (fixBody f)
        return $ Fix $ f { fixArgs = ctxn, fixType = tpn, fixBody = bodyn }

      nF (Intro s t) = Intro s <$> nF t
      nF (CoIntro s t) = CoIntro s <$> nF t
      nF (SizeApp t s) = flip SizeApp s <$> nF t

instance NormalForm FixTerm where
  normalForm (FixTerm a k nm stage c tp body) =
    liftM3 (FixTerm a k nm stage) (normalForm c) (nF tp)
    (pushBind (mkBind nm (mkPi c tp)) $ nF body)


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
        patternCtx = foldr (:>) CtxEmpty . map fakeTypedPattern


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
        Just km -> substList0 args (substSizeName km annot (brBody br))
        Nothing -> __IMPOSSIBLE__
    Nothing -> __IMPOSSIBLE__ -- branch

coiotaRed :: Int -> [Term] -> [Branch] -> Term
coiotaRed cid args branches =
  case find ( (==cid) . brConstrId ) branches of
    Just br ->
      case brSize br of
        Just km -> substList0 args (brBody br)
        Nothing -> __IMPOSSIBLE__
    Nothing -> __IMPOSSIBLE__ -- branch

-- | 'muRed' @fix@ @args@ unfolds the fixpoint and applies it to the arguments
--   @args@ shoudl have a length greater or equal than the recursive argument of
--   fix and the recursive argument should be in constructor form
-- muRed :: FixTerm -> [Term] -> Term
-- -- muRed t@(Fix CoI _ _ _ _ body) args = error "Implement nu-red"
-- muRed f args = mkApp (subst (Fix f) (mkLam (fixArgs f) (fixBody f))) args
-- -- muRed _ _ = __IMPOSSIBLE__

muRed :: FixTerm -> Annot -> [Term] -> Term
muRed f s args =
  betaRed (mkBind (fixName f) (Sort Prop) :> fixArgs f) (substSizeName (getFixStage f) s (fixBody f)) (Fix f : args)


extractConstr :: Term -> Maybe (Annot, Term, [Term])
extractConstr (Intro im t) =
  case unApp t of
    (c@Constr {}, args) -> Just (im, c, args)
    _ -> Nothing
extractConstr _ = Nothing

extractCoconstr :: Term -> Maybe (SizeName, Term, [Term])
extractCoconstr (CoIntro im t) =
  case unApp t of
    (c@Constr {}, args) -> Just (im, c, args)
    _ -> Nothing
extractCoconstr _ = Nothing
