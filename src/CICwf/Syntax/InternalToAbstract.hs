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

{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}

{-|
  TODO

  - Generation of fresh names is slow (not that it matters). See freshName
  - Replace fakeBinds with CICwf.Utils.Fresh.withFresh

  - Bound variables that do not appear in the body must be dealt with:

    * for products, replace forall by "->"

    * for functions, replace name by "_"
-}

module CICwf.Syntax.InternalToAbstract where

import           CICwf.Utils.Impossible

import           Control.Exception
import           Control.Monad.Reader hiding (mapM)

import           Data.Functor
import qualified Data.Traversable     as Tr

import qualified CICwf.Syntax.Concrete      as C
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal      as I
import           CICwf.Syntax.Position
import           CICwf.TypeChecking.TCM
-- import {-# SOURCE #-} CICwf.TypeChecking.PrettyTCM


-- -- We don't need the real type of the binds for scope checking, just the names
-- -- Maybe should be moved to another place
-- fakeBinds :: (MonadTCM tcm, HasNames a) => a -> tcm b -> tcm b
-- fakeBinds b = pushCtx (mkFakeCtx b)
--   where
--     mkFakeCtx = ctxFromList . map mkFakeBind . name
--     mkFakeBind x = I.mkBind x (I.Sort Prop)

-- freshNameList :: (MonadTCM tcm) => [Name] -> tcm [Name]
-- freshNameList []     = return []
-- freshNameList (x:xs) = do x' <- freshenName x
--                           xs' <- fakeBinds x' $ freshNameList xs
--                           return $ x' : xs'

reifyAnnot :: Annot -> Maybe C.SizeExpr
reifyAnnot annot =
  case annot of
    Empty -> Nothing
    Star  -> Just $ C.SizeStar noRange
    Stage s -> case s of
      I.Infty        -> mkSizeExpr (mkName "∞") 0
      I.StageVar v n -> mkSizeExpr (mkName (show v)) n
    SizeVar s n -> mkSizeExpr s n
  where
    mkSizeExpr s n = Just $ C.SizeExpr noRange s n



class Reify a b | a -> b where
  reify :: (MonadTCM tcm) => a -> tcm b


-- reifyCtx :: (MonadTCM tcm) => Context -> tcm C.Context
-- reifyCtx ctx = do xs <- reifyBinds (bindings ctx)
--                   return $ ctxFromList xs
--    where
--      reifyBinds [] = return []
--      reifyBinds (b:bs) =
--        do t' <- reify (bindType b)
--           bs' <- pushBind b $ reifyBinds bs
--           return $ C.Bind noRange [bindName b] (mkImplicit (isImplicit b) (Just t')) : bs'

-- instance Reify a b => Reify (Arg a) (Arg b) where
--   reify = Tr.mapM reify

-- instance Reify a b => Reify [a] [b] where
--   reify = Tr.mapM reify

instance Reify Bind C.Bind where
  reify b = do
    let nm = bindName b
    tp <- Tr.mapM reify $ bindType b
    def <- Tr.mapM reify $ bindDef b
    case def of
      Just e -> return $ C.LetBind noRange nm e (Just <$> tp)
      Nothing -> return $ C.Bind noRange [nm] tp


instance Reify (Ctx Bind) (Ctx C.Bind) where
  reify CtxEmpty = return CtxEmpty
  reify (b :> ctx) = do
    b' <- reify b
    ctx' <- pushBind b $ reify ctx
    return $ b' :> ctx'

--                   do xs <- reifyBinds (bindings ctx)
   --               return $ ctxFromList xs
   -- where
   --   reifyBinds [] = return []
   --   reifyBinds (b:bs) =
   --     do t' <- reify (bindType b)
   --        bs' <- pushBind b $ reifyBinds bs
   --        return $ C.Bind noRange [bindName b] (mkImplicit (isImplicit b) (Just t')) : bs'

-- instance Reify a b => Reify (Implicit a) (Implicit b) where
--   reify x = do
--     y <- reify (implicitValue x)
--     return $ y <$ x

-- TODO: add option to print universes. If set, reify should return (Type (Just n))

instance Reify Term C.Expr where
  reify (Sort s) = return $ C.Sort noRange s

  reify (Pi ctx tp) = do
    cctx <- freshenCtx ctx tp >>= reify
    ctp <- pushCtx ctx $ reify tp
    return $ C.Pi noRange cctx ctp

  reify (Bound n) = do
    xs <- getLocalNames
    if n >= length xs
      then return $ C.Ident noRange False (mkName ("ERROR "++show n)) C.LocalIdent
      else do
      v <- getVerbosity
      if v >= 30
        then return $ C.Ident noRange False (mkName (show (xs !! n)
                                             ++ "["
                                             ++ show n ++ "]")) C.LocalIdent
        else return $ C.Ident noRange False (mkName (show (xs !! n))) C.LocalIdent
  -- reify (Meta k) = do (Just g) <- getGoal k
  --                     case goalTerm g of
  --                       Nothing -> return $ C.Meta noRange (Just (fromEnum k))
  --                       Just t  -> reify t
  reify (Lam ctx t) = do -- reifyLamBinds (Fold.toList ctx) t
    fctx <- freshenCtx ctx t
    ctx' <- reify fctx
    t' <- pushCtx fctx $ reify t
    return $ C.Lam noRange ctx' t'
  reify (Fix f) = C.Fix <$> reify f
  reify (Case c) = C.Case <$> reify c

  reify (Constr c _ pars) =
    if c == mkName "O" && null pars
    then return $ C.Number noRange 0
    else do
      pars' <- mapM reify pars
      return $ C.mkApp (C.Ident noRange False c C.ConstructorIdent) pars'


  reify (App t ts) =
    -- Special case for reification of natural numbers
    -- case O
    case (t, ts) of
      (Constr c0 _ [], [])
        | c0 == mkName "O" -> return $ C.Number noRange 0
        | otherwise        -> return $ C.Ident noRange False c0 C.ConstructorIdent

      (Constr c1 _ [], [t])
        | c1 == mkName "S" -> do
          t' <- reify t
          return $ case t' of
            C.Number _ k -> C.Number noRange (k + 1)
            _            -> C.mkApp (C.Ident noRange False (mkName "S") C.ConstructorIdent) [t']
        | otherwise -> fmap (C.App noRange (C.Ident noRange False c1 C.ConstructorIdent) explicitArg) (reify t)
      _ -> do
        e <- reify t
        es <- mapM reify ts
        return $ C.mkApp e es

  reify (Var x) = return $ C.Ident noRange False x C.GlobalIdent

  reify (Ind annot b ind pars) =
    liftM (C.mkApp ident) (mapM reify pars)
    where
      ident :: C.Expr
      ident =
        case annot of
          Empty -> C.Ident noRange b ind C.CoInductiveIdent
          Star  -> C.SApp noRange b ind C.CoInductiveIdent (C.SizeStar noRange)
          Stage s -> case s of
            I.Infty        -> C.SApp noRange b ind C.CoInductiveIdent
                              (mkSizeExpr (mkName "∞") 0)
            I.StageVar v n -> C.SApp noRange b ind C.CoInductiveIdent
                              (mkSizeExpr (mkName (show v)) n)
          SizeVar s n -> C.SApp noRange b ind C.CoInductiveIdent
                         (mkSizeExpr s n)
      mkSizeExpr = C.SizeExpr noRange

  reify (Intro a t) =
    case t of
      Constr c _ pars ->
        if c == mkName "O" && null pars
        then return $ C.Number noRange 0
        else do
          pars' <- mapM reify pars
          return $ C.Intro noRange (reifyAnnot a) $ C.mkApp (C.Ident noRange False c C.ConstructorIdent) pars'
      App (Constr c1 _ []) [arg]
        | c1 == mkName "S" -> do
          arg' <- reify arg
          return $ case arg' of
            C.Number _ k -> C.Number noRange (k + 1)
            _            -> C.Intro noRange (reifyAnnot a) $ C.mkApp (C.Ident noRange False (mkName "S") C.ConstructorIdent) [arg']
        | otherwise -> C.Intro noRange (reifyAnnot a) <$> C.App noRange (C.Ident noRange False c1 C.ConstructorIdent) explicitArg <$> reify arg
      _ -> C.Intro noRange (reifyAnnot a) <$> reify t

  reify (CoIntro x t) = C.CoIntro noRange (Just x) <$> reify t
  reify (SizeApp t a) = do
    t' <- reify t
    return $ C.SizeApp noRange  t' (reifyAnnot a)

  reify (Subset i s t) = do
    let Just i' = reifyAnnot (hat (mkAnnot i))
        Just s' = reifyAnnot s
    t' <- reify t
    return $ C.Subset noRange i' s' t'

  reify e =
    typeError noRange $ NotImplemented ("TODO reify: " ++ show e)



instance Reify ConstrType C.ConstrExpr where
  reify (ConstrType xs t) =
    -- traceTCM 40 $ text "Reifying constrained type" <+> prettyTCM xs
    --   <+> text "=>" <+> prettyTCM t
    C.ConstrExpr noRange xs <$> reify t

instance Reify (CaseKind Annot) (CaseKind (Maybe C.SizeExpr)) where
  reify CaseKind = return CaseKind
  reify (CocaseKind a) =
    return $ case a of
      Empty -> CocaseKind Nothing
      Star  -> __IMPOSSIBLE__
      Stage s -> case s of
        I.Infty        -> CocaseKind (Just (mkSizeExpr (mkName "∞") 0))
        I.StageVar v n -> CocaseKind (Just (mkSizeExpr (mkName (show v)) n))
      SizeVar s n -> CocaseKind (Just (mkSizeExpr s n))
    where
      mkSizeExpr = C.SizeExpr noRange


-- -- TODO: print properly the names of CaseIn: do not show variables not used
instance Reify CaseTerm C.CaseExpr where
  reify (CaseTerm kind arg _ asName nmInd pars cin tpRet branches) = do
    kind' <- reify kind
    indType <- getGlobal nmInd
    arg' <- reify arg
    cin' <- mapM reify cin
    let cin'' = replicate (length pars) $ C.PatternVar noRange noName
    -- traceTCM 40 $ pushCtx (renameCtx (getIndIndices indType pars) cin)
    --         $ pushBind (mkBind asName (Sort Prop))
    --         $ (text ("reifying tpret " ++ show tpRet)
    --            $$ text "in ctx" <+> (ask >>= prettyTCM))
    ret' <- pushCtx (renameCtx (getIndIndices indType pars) cin)
            $ pushBind (mkBind asName (Sort Prop)) $ reify tpRet
    branches' <- mapM reify branches
    return $
      C.CaseExpr noRange kind' arg' asName
      (Just (C.IndicesSpec noRange nmInd (cin''++cin'))) (Just ret') branches'

-- -- instance Reify CaseIn C.CaseIn where
-- --   reify cin = traverse reify cin
-- instance Reify a b => Reify (Maybe a) (Maybe b) where
--   reify = Tr.mapM reify

instance Reify FixTerm C.FixExpr where
  reify (FixTerm k num f spec args tp body) = do
    args' <- reify args
    tp'   <- pushCtx args $ reify tp
    let recTp = mkPi args tp
    -- f'    <- freshenName f
    body' <- pushBind (mkBind f recTp) $ pushCtx args $ reify body
    return $ C.FixExpr noRange k f spec' args' tp' body'
    where
      argNames :: [Name]
      argNames = concatMap name (bindings args)
      spec' = case spec of
        FixPosition -> C.FixPosition
        FixStruct   -> C.FixStruct noRange (argNames !! num)
        FixStage nm -> C.FixStage noRange nm

instance Reify Branch C.Branch where
  reify (Branch sv nmConstr idConstr patt body) = do
    constr <- getGlobal nmConstr
    patt' <- mapM reify patt
    let patCtx = replicate (length patt) $ mkBind noName (Sort Prop)
    body' <- pushCtx (renameCtx (ctxFromList patCtx) patt)
             $ reify body
    return $ C.Branch noRange sv nmConstr patt' body'

-- instance Reify Subst C.Subst where
--   reify (Subst sg) =
--     do sg' <- mapM reifyAssign sg
--        return $ C.Subst sg'
--       where reifyAssign (k, t) = do xs <- getLocalNames
--                                     e <- reify t
--                                     return $ C.Assign noRange (xs !! k) k e

-- instance Reify I.Bind C.Bind where
--   reify b = liftM mkB (reify (I.bindType b))
--     where
--       mkB e = C.mkBind noRange (I.bindName b) (isImplicit b) e

instance Reify SinglePattern C.SinglePattern where
  reify (PatternVar x) = return $ C.PatternVar noRange x
  reify (PatternDef x t) = fmap (C.PatternDef noRange x) (reify t)


instance Reify (Named I.Global) C.Declaration where
  reify g = reifyGlobal (namedValue g)
    where
      nm = nameTag g
      reifyGlobal :: (MonadTCM tcm) => I.Global -> tcm C.Declaration
      reifyGlobal d@(I.Definition {}) = do
        eTp <- reify (defType d)
        eDef <- reify (defTerm d)
        return $ C.Definition noRange nm (Just eTp) eDef
      reifyGlobal d@(I.Assumption {}) = do
        e <- reify (assumeType d)
        return $ C.Assumption noRange nm e

      reifyGlobal t@(I.Inductive {}) = do
        pars <- reify (I.indPars t)
        tp   <- pushCtx (indPars t) $ reify (mkPi (I.indIndices t) (I.Sort (I.indSort t)))
        constrs <- mapM reifyConstrInd (I.indConstr t)
        return $ C.Inductive noRange (C.InductiveDef nm (I.indKind t) pars (I.indPol t) tp constrs)

      reifyGlobal (Constructor {}) = __IMPOSSIBLE__

      reifyGlobal d@(I.Cofixpoint {}) = do
        f' <- reify (cofixTerm d)
        return $ C.Cofixpoint f'

      constrType :: (MonadTCM tcm) => Name -> tcm (Context, Type)
      constrType x = do
        c@(Constructor {}) <- getGlobal x
        let numPars = ctxLen (I.constrPars c)
            numArgs = ctxLen (I.constrArgs c)
            pars = map Bound (reverse [numArgs..numArgs+numPars-1])
            tp = mkPi (I.constrArgs c) (mkApp (Ind Empty True (I.constrInd c) pars) (I.constrIndices c))
        return (I.constrPars c, tp)

      reifyConstrInd :: (MonadTCM tcm) => Name -> tcm C.Constructor
      reifyConstrInd x = do
        (ctx, tp) <- constrType x
        -- let eraseStar s = if s == Star then Empty else s
        let eraseStar s = s
        e <- pushCtx ctx $ reify (modifySize eraseStar tp)
        return $ C.Constructor noRange x e


--   -- Special case for reification of natural numbers
--   -- case O
--   concretize (Constr (Id (Just "O")) cid []) = return $ C.Number noRange 0
--   concretize (Var (Id (Just "O"))) = return $ C.Number noRange 0
--   -- concretize (Ind _ (Id (Just "O"))) = return $ C.Number noRange 0
--   -- case S
--   concretize (Constr (Id (Just "S")) cid [t]) = do
--     t' <- concretize t
--     return $ case t' of
--       C.Number noRange k -> C.Number noRange (k + 1)
--       _                  -> C.Constr noRange (mkName "S") cid [t']
--   concretize (App (Constr (Id (Just "S")) cid []) [t]) = do
--     t' <- concretize t
--     return $ case t' of
--       C.Number noRange k -> C.Number noRange (k + 1)
--       _                  -> C.mkApp (C.Constr noRange (mkName "S") cid []) [t']
--   concretize (App (Var (Id (Just "S"))) [t]) = do
--     t' <- concretize t
--     return $ case t' of
--       C.Number noRange k -> C.Number noRange (k + 1)
--       _                  -> C.App noRange (C.Ident noRange (mkName "S")) t'
-- -- concretize (App (Ind a (Id (Just "S"))) [t]) =
-- --   do t' <- concretize t
-- --      return $ case t' of
-- --        C.Number noRange k -> C.Number noRange (k + 1)
-- --        _                  -> C.App noRange (C.Ind noRange a (mkName "S") []) t'
