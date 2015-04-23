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
{-# LANGUAGE UndecidableInstances   #-}

{-|
  TODO

  - Generation of fresh names is slow (not that it matters). See freshName

  - Bound variables that do not appear in the body must be dealt with:

    * for products, replace forall by "->"

    * for functions, replace name by "_"

  - Add option to show Universes/implicit arguments
-}

module CICwf.Syntax.AbstractToConcrete where

#include "undefined.h"
import           CICwf.Utils.Impossible

import           Control.Applicative

import qualified Data.Traversable        as Tr

import qualified CICwf.Syntax.Abstract   as A
import           CICwf.Syntax.Common
import qualified CICwf.Syntax.Concrete   as C
import           CICwf.Syntax.Position
import           CICwf.Syntax.ScopeMonad
import           CICwf.TypeChecking.TCM


class ToConcrete a b | a -> b where
  concretize :: (MonadTCM tcm) => a -> tcm b


instance (ToConcrete a b, HasNames a) => ToConcrete (Ctx a) (Ctx b) where
  concretize CtxEmpty  = return CtxEmpty
  concretize (x :> xs) = do
    y  <- concretize x
    ys <- extendScope (name x) $ concretize xs
    return $ y :> ys


instance ToConcrete A.Bind C.Bind where
  concretize (A.Bind _ xs arg) = do
    arg' <- concretize arg
    return $ C.Bind noRange xs arg'
  concretize (A.LetBind _ x e1 arg) = do
    e1'  <- concretize e1
    arg' <- concretize arg
    return $ C.LetBind noRange x e1' arg'
  concretize (A.BindName _ arg x) = return $ C.BindName noRange arg x


instance ToConcrete a b => ToConcrete (Arg a) (Arg b) where
  concretize = Tr.mapM concretize


instance (ToConcrete a b, ToConcrete c d) => ToConcrete (a,c) (b,d) where
  concretize (x, y) = do
    x' <- concretize x
    y' <- concretize y
    return (x', y')


instance ToConcrete a b => ToConcrete (Maybe a) (Maybe b) where
  concretize = Tr.mapM concretize


instance ToConcrete a b => ToConcrete [a] [b] where
  concretize = Tr.mapM concretize


instance ToConcrete A.Expr C.Expr where
  concretize (A.Ann _ e1 e2) = do
    e1' <- concretize e1
    e2' <- concretize e2
    return $ C.Ann noRange e1' e2'
  concretize (A.Sort _ s) = return $ C.Sort noRange s
  concretize (A.Pi _ ctx t) = do
    ctx' <- concretize ctx
    t'   <- extendScope (name ctx) $ concretize t
    return $ C.Pi noRange ctx' t'
  concretize (A.Local _ x) = return $ C.Ident noRange False x C.LocalIdent
  concretize (A.Global _ x) = return $ C.Ident noRange False x C.GlobalIdent
  concretize (A.SApp _ b x s) = do
    s' <- concretize s
    return $ C.SApp noRange b x C.UnknownIdent s'
  concretize (A.Lam _ ctx t) = do -- concretizeLamBinds (Fold.toList ctx) t
    ctx' <- concretize ctx
    t'   <- extendScope (name ctx) $ concretize t
    return $ C.Lam noRange ctx' t'
  concretize (A.Case c) = C.Case <$> concretize c
  concretize (A.Fix f b) = flip C.Fix b <$> concretize f
  concretize (A.Ind _ b ind annot pars) = do
    pars' <- mapM concretize pars
    annot' <- concretize annot
    case annot of
      A.SizeEmpty -> return $ C.mkApp (C.Ident noRange b ind C.CoInductiveIdent ) pars'
      _           -> return $ C.mkApp (C.SApp noRange b ind C.CoInductiveIdent annot') pars'

  -- Special case for reification of natural numbers
  -- case O
  concretize (A.Constr _ (Id (Just "O")) []) = return $ C.Number noRange 0
  concretize (A.App _ (A.Constr _ (Id (Just "S")) []) _ t) = do
    t' <- concretize t
    return $ case t' of
      C.Number noRange k -> C.Number noRange (k + 1)
      _                  -> C.mkApp (C.Ident noRange False (mkName "S") C.ConstructorIdent) [t']

  concretize (A.App _ e1 t e2) = do
    e1' <- concretize e1
    e2' <- concretize e2
    return $ C.App noRange e1' t e2'

  concretize (A.Constr _ x ps) = do
    ps' <- mapM concretize ps
    return $ C.mkApp (C.Ident noRange False x C.ConstructorIdent) ps'

  concretize (A.Intro _ s e) = do
    e' <- concretize e
    s' <- concretize s
    return $ C.Intro noRange s' e'

  concretize (A.CoIntro _ s1 s2 e) = do
    e' <- concretize e
    s1' <- concretize s1
    s2' <- concretize s2
    return $ C.CoIntro noRange s1' s2' e'

  concretize (A.SizeApp r e s) = do
    e' <- concretize e
    s' <- concretize s
    return $ C.SizeApp noRange e' s'

-- -- Well-founded sizes
--   | Intro Range (Maybe SizeExpr) Expr
--   | CoIntro Range (Maybe SizeName) Expr
--   | SizeApp Range Expr (Maybe SizeExpr)




instance ToConcrete A.SizeExpr C.SizeExpr where
  concretize (A.SizeExpr _ x n) = return $ C.SizeExpr noRange x n
  concretize (A.SizeStar _) = return $ C.SizeStar noRange
  concretize A.SizeEmpty = return $ C.SizeExpr noRange (mkName "○") 0
  concretize A.SizeInfty = return $ C.SizeExpr noRange (mkName "∞") 0

instance ToConcrete A.SizeName C.SizeName where
  concretize = return

-- TODO: print properly the names of CaseIn: do not show variables not used
instance ToConcrete A.CaseExpr C.CaseExpr where
  concretize (A.CaseExpr _ kind arg nmArg indices ret branches) = do
    kind'     <- Tr.mapM concretize kind
    arg'      <- concretize arg
    indices'  <- concretize indices
    ret'      <- extendScope (name indices) $ extendScope (name nmArg)
            $ concretize ret
    branches' <- mapM (extendScope (name indices) . concretize) branches
    return $
      C.CaseExpr noRange kind' arg' nmArg indices'  ret' branches'


instance ToConcrete A.IndicesSpec C.IndicesSpec where
  concretize (A.IndicesSpec _ ind args) = do
    args' <- concretize args
    return $ C.IndicesSpec noRange ind args'


instance ToConcrete A.SinglePattern C.SinglePattern where
  concretize (A.PatternVar r x) = return $ C.PatternVar r x
  concretize (A.PatternDef r x e) = C.PatternDef r x <$> concretize e


instance ToConcrete A.FixExpr C.FixExpr where
  concretize (A.FixExpr _ k f spec args tp body) = do
    args' <- specScope $ concretize args
    tp'   <- extendScope (name args) $ concretize tp
    body' <- specScope
             $ extendScope (name args)
             $ extendScope (name f) $ concretize body
    spec' <- concretizeSpec spec
    return $ C.FixExpr noRange k f spec' args' tp' body'
    where
      argNames :: [Name]
      argNames = concatMap name (bindings args)
      specScope = case spec of
        A.FixStruct _ _ -> extendScope []
        A.FixPosition _ -> extendScope []
        A.FixStage _ x _ -> extendScope [x]
      concretizeSpec sp = case sp of
        A.FixStruct _ i -> return $ C.FixStruct noRange (argNames !! i)
        A.FixPosition _ -> return C.FixPosition
        A.FixStage _ x _ -> return $ C.FixStage noRange x


instance ToConcrete A.Branch C.Branch where
  concretize (A.Branch _ sv nmConstr _ args body) = do
    args' <- concretize args
    body' <- extendScope (name args) $ concretize body
    return $ C.Branch noRange sv nmConstr args' body'


instance ToConcrete A.ConstrExpr C.ConstrExpr where
  concretize (A.ConstrExpr _ xs e) = do
    e' <- extendScope xs $ concretize e
    return $ C.ConstrExpr noRange xs e'


instance ToConcrete A.Declaration C.Declaration where
  concretize (A.Definition r x t u) = do
    t' <- concretize t
    u' <- concretize u
    return $ C.Definition r x t' u'
  concretize (A.Assumption r x t) = do
    t' <- concretize t
    return $ C.Assumption r x t'
  concretize (A.Cofixpoint f) = C.Cofixpoint <$> concretize f
  concretize (A.Inductive rg i) = C.Inductive rg <$> concretize i
  concretize (A.Check e1 e2) = do
    e1' <- concretize e1
    e2' <- concretize e2
    return $ C.Check e1' e2'
  concretize (A.Print _ x) = return $ C.Print noRange x
  concretize (A.Eval e) = do
    e' <- concretize e
    return $ C.Eval e'

instance ToConcrete A.InductiveDef C.InductiveDef where
  concretize (A.InductiveDef x k pars pols tp constrs) = do
    pars' <- concretize pars
    tp' <- extendScope (name pars) $ concretize tp
    constrs' <- extendScope (name pars) $
                extendScope [x] $ mapM concretize constrs
    return $ C.InductiveDef x k pars' pols tp' constrs'


instance ToConcrete A.Constructor C.Constructor where
  concretize (A.Constructor rg x tp) = do
    tp' <- concretize tp
    return (C.Constructor rg x tp')
