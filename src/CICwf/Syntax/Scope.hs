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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}

-- | Scope checking of C.Declaration and C.Expr.
--
-- It replaces
-- * Var x           --> Bound n  for bound variables
-- * App (Var i ...) --> Ind i ...     for inductive types, checking they are
--                                     applied to parameters
-- * App (Var c ...) --> Constr c j ...   for constructors, checking they are
--                                        fully applied
--
-- We also check that names of global declarations are not defined

-- TODO: check pattern linearity and constraint type linearity

module CICwf.Syntax.Scope(
  scope) where

import           CICwf.Utils.Impossible

import           Control.Exception
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Function
import           Data.Functor
import           Data.List
import           Data.Maybe

import qualified CICwf.Syntax.Abstract        as A
import           CICwf.Syntax.Common
import qualified CICwf.Syntax.Concrete        as C
import qualified CICwf.Syntax.Internal        as I
import           CICwf.Syntax.Position
import CICwf.Syntax.ScopeMonad

import  CICwf.TypeChecking.PrettyTCM
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors

import           CICwf.Utils.Sized


-- | We reuse the type-checking monad for scope checking
--   TODO: maybe move these function somewhere else
-- class Scope a b | a -> b where
--   scope :: MonadTCM m => a -> m b


-- getScope :: MonadTCM tcm => tcm LocalScope
-- getScope = stScope <$> get


-- setScope :: MonadTCM tcm => LocalScope -> tcm ()
-- setScope s = do
--   st <- get
--   put $ st { stScope = s }


-- withScope :: MonadTCM tcm => LocalScope -> tcm a -> tcm a
-- withScope s = localScope (const s)


-- localScope :: MonadTCM tcm => (LocalScope -> LocalScope) -> tcm a -> tcm a
-- localScope f m = do
--   s <- getScope
--   setScope (f s)
--   x <- m
--   setScope s
--   return x


-- extendScope :: MonadTCM tcm => [Name] -> tcm a -> tcm a
-- extendScope s = localScope (\s' -> s' <:> ctxFromList s)


-- getSizeScope :: MonadTCM tcm => tcm LocalScope
-- getSizeScope = stSizeScope <$> get


-- setSizeScope :: MonadTCM tcm => LocalScope -> tcm ()
-- setSizeScope s = do
--   st <- get
--   put $ st { stSizeScope = s }


-- withSizeScope :: MonadTCM tcm => LocalScope -> tcm a -> tcm a
-- withSizeScope s = localSizeScope (const s)


-- localSizeScope :: MonadTCM tcm => (LocalScope -> LocalScope) -> tcm a -> tcm a
-- localSizeScope f m = do
--   s <- getSizeScope
--   setSizeScope (f s)
--   x <- m
--   setSizeScope s
--   return x


-- extendSizeScope :: MonadTCM tcm => [Name] -> tcm a -> tcm a
-- extendSizeScope s = localSizeScope (\s' -> s' <:> ctxFromList s)


------------------------------------------------------------
-- * Scope checking
------------------------------------------------------------

linearCheck :: [Name] -> Bool
linearCheck xs = ys == nub ys
  where
    ys = filter (not . isNull) xs


instance Scope a b => Scope (Maybe a) (Maybe b) where
    scope (Just x) = do s <- scope x
                        return $ Just s
    scope Nothing = return Nothing


instance Scope a b => Scope (Implicit a) (Implicit b) where
  scope x = do v <- scope (implicitValue x)
               return $ v <$ x


instance Scope a b => Scope [a] [b] where
  scope = mapM scope


instance Scope C.Expr A.Expr where
  scope (C.Ann r e1 e2) = do
    e1' <- scope e1
    e2' <- scope e2
    return $ A.Ann r e1' e2'
  scope (C.Sort r s) = return $ A.Sort r s
  scope (C.Pi r ctx e) = do
    ctx' <- scope ctx
    e' <- extendScope (name ctx) $ scope e
    return $ A.Pi r ctx' e'
  scope (C.Lam r bs e) = do
    bs' <- scope bs
    -- liftIO $ print ("scope lam " ++ show bs)
    e' <- extendScope (name bs) $ scope e
    return $ A.Lam r bs' e'
  scope e@(C.App r e1 t e2) = scopeApp (C.unApp e)
    -- e1' <- scope e1
    -- e2' <- scope e2
    -- return $ A.App r e1' t e2'
  scope e@(C.SApp _ _ _ _ _) = scopeApp (e, [])
  scope (C.Meta r i) = return $ A.Meta r i
  scope e@(C.Ident _ _ _ _) = scopeApp (e, [])
  scope (C.Case c) = fmap A.Case (scope c)
  scope (C.Fix f) = fmap A.Fix (scope f)
  scope (C.Number r n) = return $ mkNat n
    where
      mkNat 0 = A.Constr r (mkName "O") []
      mkNat k = A.App r (A.Constr r (mkName "S") []) explicitArg (mkNat (k-1))

  scope (C.Intro r Nothing e) = fmap (A.Intro r Nothing) (scope e)
  scope (C.CoIntro r Nothing e) = fmap (A.CoIntro r Nothing) (scope e)

newtype AppScope = AppScope (C.Expr, [(ArgType, C.Expr)])
                   deriving(Show)


instance Scope C.SizeExpr A.SizeExpr where
  scope (C.SizeExpr r x n) = do
    xs <- getSizeScope
    -- liftIO $ print ("scope ident " ++ show x ++ " in " ++ show xs)
    case findIndex (==x) (envToList xs) of
      Just _ -> return $ A.SizeExpr r x n
      Nothing -> scopeError r $ UndefinedName x
  scope (C.SizeStar r) = return $ A.SizeStar r


instance (Scope a b, HasNames a) => Scope (Ctx a) (Ctx b) where
  scope CtxEmpty = return CtxEmpty
  scope (x :> xs) = do
    y  <- scope x
    ys <- extendScope (name x) $ scope xs
    return $ y :> ys


instance Scope C.Bind A.Bind where
  scope (C.Bind r ns tp) = do
    tp' <- scope tp
    return $ A.Bind r ns tp'
  scope (C.LetBind r x e tp) = do
    e'  <- scope e
    tp' <- scope tp
    return $ A.LetBind r x e' tp'
  scope (C.BindName r t x) =
    return $ A.BindName r t x


instance Scope a b => Scope (Arg a) (Arg b) where
  scope arg = do
    y <- scope (unArg arg)
    return $ y <$ arg


instance Scope C.FixExpr A.FixExpr where
  scope (C.FixExpr rg ki f spec args tp body) =
    do args' <- specScope $ scope args
       unless (linearCheck argNames) $ typeError rg $ NotImplemented "non-linear context"
       tp'   <- specScope
                $ extendScope (name args) $ scope tp
       -- spec' <- extendScope (name args) $ scope spec
       spec' <- scopeSpec spec
       traceTCM 70 $ (text "Scoping fix body" <+> prettyTCM body
                     $$ text "adding names" <+> prettyTCM (name f ++name args))
       body' <- specScope
                $ extendScope (name f) $ extendScope (name args) $ scope body
       return $ A.FixExpr rg ki f spec' args' tp' body'
    where
      argNames = concatMap name (bindings args)
      specScope = case spec of
        C.FixStruct _ _ -> extendScope []
        C.FixPosition -> extendScope []
        C.FixStage _ x -> extendSizeScope [x]
      scopeSpec sp = case sp of
        C.FixStruct r x ->
          case findIndex (==x) argNames of
            Just i -> do traceTCM 70 $ text "RECARG" <+> prettyTCM i
                         return $ A.FixStruct r i
            Nothing -> undefinedName r x
        C.FixPosition -> case findRecArg (bindings args) 0 of
                           Just n -> do
                             traceTCM 70 $ text "RECARG" <+> prettyTCM n
                             return $ A.FixPosition n
                           Nothing ->
                             case ki of
                               I -> typeError rg $ NotImplemented "Specify fix spec"
                               CoI -> return $ A.FixPosition (-1)
        C.FixStage r x -> case findRecArg (bindings args) 0 of
                           Just n -> do
                             traceTCM 70 $ text "RECARG" <+> prettyTCM n
                             return $ A.FixStage r x n
                           Nothing ->
                             case ki of
                               I -> notImplemented rg "Specify fix spec"
                               CoI -> return $ A.FixStage r x (-1)
      findRecArg :: [C.Bind] -> Int -> Maybe Int
      findRecArg [] _ = Nothing
      findRecArg (C.Bind _ xs t:bs) n =
        if C.hasStar (unArg t) || C.hasSize (unArg t)
        then Just n
        else findRecArg bs (n + length xs)
      findRecArg (C.BindName {}:bs) n = findRecArg bs (n+1)
      findRecArg (C.LetBind {}:bs) n = findRecArg bs (n+1)
      -- TODO: check for stars in the LetBind case


-- instance Scope C.FixSpec A.FixSpec where
--   scope (C.FixStruct r x) = do
--     xs <- getScope
--     -- liftIO $ print ("scope ident " ++ show x ++ " in " ++ show xs)
--     case findIndex (==x) (envToList xs) of
--       Just _  -> return $ A.FixStruct r x
--       Nothing -> undefinedName r x
--   scope C.FixPosition = return A.FixPosition
--   scope (C.FixStage r x) = return $ A.FixStage r x


instance Scope C.CaseExpr A.CaseExpr where
  scope (C.CaseExpr r kind arg asName indices ret bs) =
    do arg'     <- scope arg
       let kind' = case kind of
             CaseKind -> CaseKind
             CocaseKind Nothing -> CocaseKind Nothing
             CocaseKind (Just _) -> __IMPOSSIBLE__
       unless (linearCheck (name indices)) $
         notImplemented (range indices) "non-linear pattern"
       indices' <- scope indices
       traceTCM 70 $ extendScope (name indices) $
         extendScope (name asName) $
           (text "scoping ret" <+> prettyTCM ret
            $$ text "in env" <+> (getScope >>= prettyTCM))
       ret'     <- extendScope (name indices) $
                   extendScope (name asName) $ scope ret
       bs'      <- mapM scope bs
       let sortbs = sortBy (compare `on` A.brConstrId) bs'
       return $ A.CaseExpr r kind' arg' asName indices' ret' sortbs


instance Scope C.IndicesSpec A.IndicesSpec where
  scope (C.IndicesSpec r nm ctx) =
    do g <- lookupGlobal nm
       case g of
         Just ind@(I.Inductive {}) -> do
           ctx' <- scope ctx
           traceTCM 70 $ text ("Scoped indices " ++ show ctx)
           -- Check that the inductive type is applied to the right number
           -- of arguments
           when (size ctx /= numPars + numArgs) $
             notImplemented r ("wrong number of arguments in indices")
           -- Check that parameters are all '_'
           unless (all parIsNull pars)
             $ typeError r $ NotImplemented "Error: parameters in case indices must be _"
           -- Check that indices are variables or of the form (x := t)
           return $ A.IndicesSpec r nm ctx'
             where
               numPars = size (I.indPars ind)
               numArgs = size (I.indIndices ind)
               (pars, _) = splitAt numPars ctx
               parIsNull (C.PatternVar _ x) = isNull x
               parIsNull _                  = False
               argIsVarOrDef (C.BindName _ _ x) = True
               argIsVarOrDef (C.LetBind _ _ _ e) = isNothing (unArg e)

         Just _                -> scopeError r $ NotInductive nm
         Nothing               -> scopeError r $ UndefinedName nm


instance Scope C.SinglePattern A.SinglePattern where
  scope (C.PatternVar r x) = return $ A.PatternVar r x
  scope (C.PatternDef r x e) = fmap (A.PatternDef r x) (scope e)

-- TODO: check that all branch belong to the same inductive type, and that all
--       constructors of the inductive type are considered
instance Scope C.Branch A.Branch where
  scope (C.Branch r sv constr pattern body) = do
    traceTCM 70 $ text ("branch --> " ++ show constr ++ " " ++ show (name pattern))
    unless (linearCheck (name pattern)) $
      notImplemented r "non-linear branch pattern"
    g <- lookupGlobal constr
    case g of
      Just (I.Constructor _ idConstr _ targs _ _) -> do
        traceTCM 70 $ hsep [ text "pattern"
                           , prettyTCM lenPat
                           , text ":"
                           , text (show pattern) ]
                      $$ hsep [ text "against args"
                              , prettyTCM lenArgs
                              , text ":"
                              , prettyTCM targs ]
        when (lenPat /= lenArgs) $ wrongArg r constr lenPat lenArgs
        pattern' <- scope pattern
        body'    <- extendScope (name pattern) $ scope body
        return $ A.Branch r sv constr idConstr pattern' body'
          where lenPat  = length pattern
                lenArgs = size targs
      Just _  -> scopeError r $ PatternNotConstructor constr
      Nothing -> do
        traceTCM 70 $ text (show constr ++ " not found\n")
        typeError r $ UndefinedName constr


-- scopeAssign :: (MonadTCM tcm) => Int -> A.Assign -> tcm A.Assign
-- scopeAssign k an = do xs <- getLocalNames
--                       case findIndex (==A.assgnName an) xs of
--                         Just n | n < k -> do e' <- scope (A.assgnExpr an)
--                                              return $ an { A.assgnBound = n,
--                                                            A.assgnExpr = e' }
--                                | otherwise -> error "scope: assign var out of bound"
--                         Nothing -> error "scope: var not found"


-- scopeSubst :: (MonadTCM tcm) => Int -> A.Subst -> tcm A.Subst
-- scopeSubst k (A.Subst sg) = mapM (scopeAssign k) sg >>= return . A.Subst


scopeApp :: (MonadTCM tcm) => (C.Expr, [(ArgType, C.Expr)]) -> tcm A.Expr
scopeApp (func, args) = do
  traceTCM 70 $ vcat [ text "Scoping" <+> prettyTCM func
                     , text "with args" <+> prettyTCM (map snd args) ]
  args' <- scope (map snd args)
  case func of
    e@(C.Ident r b x _) -> do
      xs <- getScope
      case findIndex (==x) (envToList xs) of
        Just n -> return $ A.mkApp (A.Local r x) args'
        Nothing -> do
          g <- lookupGlobal x
          case g of
            Just i@(I.Inductive {}) ->
                do
                  traceTCM 70 $ vcat [ text "Inductive" <+> prettyTCM x
                                    , text "args: " <+> prettyTCM args'
                                    , text "given pars:" <+> prettyTCM givenLen <+> prettyTCM parLen ]
                  if givenLen < parLen
                    then inductiveNotApplied iRange x
                    else return (A.mkApp (A.Ind iRange b x A.SizeEmpty ipars) iargs)
                where
                  parLen = size (I.indPars i)
                  argLen = size (I.indIndices i)
                  givenLen = length args
                  (ipars, iargs) = splitAt parLen args'
                  iRange = fuseRange r args'
            Just (I.Constructor i idConstr parsTp argsTp _ _) -> do
              traceTCM 70 $ text "scoping constructor"
                <+> prettyTCM i <+> prettyTCM idConstr
                $$ nest 2 (text "expected args" <+> prettyTCM expLen
                           <+> prettyTCM parsTp
                           $$ text "given args" <+> prettyTCM givenLen)
              if givenLen < expLen
                then wrongArg cRange x expLen givenLen
                else return $ A.mkApp (A.Constr cRange x cpars) cargs
                where
                  parLen = size parsTp
                  argLen = size argsTp
                  givenLen = length args
                  expLen = parLen
                  (cpars, cargs) = splitAt parLen args'
                  cRange = fuseRange r cpars
            Just _ -> return $ A.mkApp (A.Global r x) args'
            Nothing -> undefinedName r x
    e@(C.SApp r b x _ s) -> do
      s' <- scope s
      xs <- getScope
      case findIndex (==x) (envToList xs) of
        Just _ -> notImplemented r " SApp local"
        Nothing ->
          do g <- lookupGlobal x
             case g of
               Just i@(I.Inductive {}) -> do
                  if givenLen < parLen
                    then inductiveNotApplied iRange x
                    else return (A.mkApp (A.Ind iRange b x s' ipars) iargs)
                where
                  parLen = size (I.indPars i)
                  argLen = size (I.indIndices i)
                  givenLen = length args
                  (ipars, iargs) = splitAt parLen args'
                  iRange = fuseRange r args'
               Just (I.Constructor {}) -> notImplemented r ("SApp constr" ++ show x)
               Just (I.Definition {})  -> notImplemented r ("TODO: SApp definition")
               Just (I.Assumption {})  -> notImplemented r $ "SApp assumption " ++ show x
               Nothing                 -> undefinedName r x

    -- Not an identifier, nor a size application
    e -> do
      e' <- scope e
      return $ A.mkApp e' args'


instance Scope C.ConstrExpr A.ConstrExpr where
  scope (C.ConstrExpr r xs e) = do
    e' <- extendSizeScope xs $ scope e
    return $ A.ConstrExpr r xs e'


instance Scope C.Declaration A.Declaration where
  scope (C.Definition r x t u) = do
    t' <- scope t
    u' <- scope u
    failIfDefined x
    return $ A.Definition r x t' u'
  scope (C.Assumption r x t) = do
    t' <- scope t
    failIfDefined x
    return $ A.Assumption r x t'
--     scope (A.Inductive r indDef) = fmap (A.Inductive r) (scope indDef)
  scope (C.Eval e) = do
    e' <- scope e
    return $ A.Eval e'
  scope (C.Check e1 e2) = do
    e1' <- scope e1
    e2' <- scope e2
    return $ A.Check e1' e2'
  scope (C.Print rg x) = do
    g <- lookupGlobal x
    case g of
      Just _ -> return $ A.Print rg x
      Nothing -> undefinedName rg x

  scope (C.Cofixpoint f) = fmap A.Cofixpoint $ scope f
  scope (C.Inductive rg i) = fmap (A.Inductive rg) $ scope i


instance Scope C.InductiveDef A.InductiveDef where
  scope (C.InductiveDef x k pars pols tp constrs) = do
    pars' <- scope pars
    tp' <- extendScope (name pars) $ scope tp
    constrs' <- extendScope (name pars) $
                extendScope [x] $ mapM scope constrs
    failIfDefined x
    return $ A.InductiveDef x k pars' pols tp' constrs'


instance Scope C.Constructor A.Constructor where
  scope (C.Constructor rg x tp) = do
    tp' <- scope tp
    failIfDefined x
    return (A.Constructor rg x tp')
