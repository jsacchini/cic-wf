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

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module CICwf.TypeChecking.Conversion where

#include "undefined.h"
import CICwf.Utils.Impossible

import Control.Applicative
import Control.Monad.State

import CICwf.Syntax.Common
import CICwf.Syntax.Position
-- import CICwf.Syntax.Size
import CICwf.Syntax.Internal
import CICwf.TypeChecking.Constraints
import CICwf.TypeChecking.PrettyTCM
import CICwf.TypeChecking.TCM
import CICwf.TypeChecking.Whnf
import CICwf.Utils.Misc


(<<=) :: Annot -> Annot -> [Constraint StageNode]
(<<=) (Stage sta1) (Stage sta2) = leStage sta1 sta2
  where
    leStage (StageVar s1 n1) (StageVar s2 n2) = [(VarNode s1, VarNode s2, n2 - n1)]
    leStage (StageVar _ _) Infty              = []
    leStage Infty            (StageVar s2 _)  = [(InftyNode, VarNode s2, 0)]
    leStage Infty            Infty            = []
(<<=) _          _          = []


(<<>>) :: Annot -> Annot -> [Constraint StageNode]
(<<>>) a1 a2 = a1 <<= a2 ++ a2 <<= a1


subSort :: (MonadTCM tcm) => Sort -> Sort -> tcm Bool
subSort Prop     Prop     = return True -- Prop ⊈ Type(i)
subSort (Type m) (Type n) = return (m <= n)
subSort _        _        = return False


subConstrType :: (MonadTCM tcm) => Type -> ConstrType -> tcm Bool
subConstrType t1 (ConstrType i t2) =
  pushWfDecl i infty $ subType t1 t2
subConstrType t1 (UnConstrType t2) = subType t1 t2

data ConversionTest = Conv -- ^ Test for conversion
                    | Leq  -- ^ Test for subtyping
                    | LeqSort -- ^ Test for subtyping and universe inclusion Type(i) &#x3BB; Type(j)   if i ≤ j
                    deriving(Show)

class NormalForm a => Conversion a where
  -- We assume that both arguments are in normal form
  -- TODO: A more efficient version would only assume whnf
  convTest :: (MonadTCM tcm) => ConversionTest -> a -> a -> tcm Bool

  subType :: (MonadTCM tcm) => a -> a -> tcm Bool
  subType t1 t2 = do
    n1 <- normalForm t1
    n2 <- normalForm t2
    convTest LeqSort n1 n2

  conv :: (MonadTCM tcm) => a -> a -> tcm Bool
  conv t1 t2 = do
    n1 <- normalForm t1
    n2 <- normalForm t2
    convTest Conv n1 n2


instance Conversion a => Conversion (Maybe a) where
  convTest ct Nothing Nothing = return True
  convTest ct (Just x) (Just y) = convTest ct x y
  convTest _ _ _ = return False

instance Conversion a => Conversion [a] where
  convTest ct [] [] = return True
  convTest ct (t1:ts1) (t2:ts2) = convTest ct t1 t2 `mAnd` convTest ct ts1 ts2
  convTest ct _ _ = return False

instance Conversion Sort where
  convTest _ Prop     Prop      = return True
  convTest ct (Type m) (Type n) =
    case ct of
      Conv    -> return (m == n)
      Leq     -> return (m == n)
      LeqSort -> return (m <= n)
  convTest _ _ _                = return False


instance Conversion Type where
  convTest ct (Sort s1) (Sort s2) = convTest ct s1 s2
  convTest ct t@(Pi _ _) u@(Pi _ _) =
    convTest ct1 uctx tctx `mAnd` pushCtx uctx (convTest ct2 t' u')
      where
        (tctx, t') = unPi t
        (uctx, u') = unPi u
        (ct1, ct2) = case ct of
                       Conv -> (Conv, Conv)
                       Leq -> (Leq, Leq)
                       LeqSort -> (Leq, LeqSort)
  convTest ct t1@(Ind a1 b1 x1 ps1) t2@(Ind a2 b2 x2 ps2)
    | x1 == x2 && b1 == b2 =
        do
          traceTCM 40 $ (text "convtest" <+> prettyTCM t1 <+> text "~~~"
                         <+> prettyTCM t2)
          a1' <- getStage a1
          a2' <- getStage a2
          ind <- getGlobal x1
          traceTCM 40 $ text "Adding constraints:"<+> prettyTCM (mkConstraint (indKind ind) a1' a2')
          -- addStageConstraints (mkConstraint (indKind ind) a1' a2')
          mkWfConstraint (indKind ind) addWfConstraint a1' a2'
          case ind of
            Inductive {} -> mAll (zipWith3 (convPars ct) (indPol ind) ps1 ps2)
            _ -> __IMPOSSIBLE__ -- sanity check
    | otherwise = return False
    where
      getStage :: (MonadTCM tcm) => Annot -> tcm Annot
      getStage s@(SizeVar nm k) = do
        traceTCM 30 $ text "sizeMap" <+> (getSizeMap >>= prettyTCM)
        sv0 <- getSize nm
        case sv0 of
          Just sv -> return $ hatn k sv
          Nothing -> return s
      getStage s@(Stage _) = return s
      getStage s = traceTCM 1 (text "getStage" <+> prettyTCM s) >> __IMPOSSIBLE__
      mkConstraint ki = case ct of
                         Conv -> (<<>>)
                         _ -> case ki of
                                I -> (<<=)
                                CoI -> flip (<<=)
      mkWfConstraint ki f = case ct of
                              Conv -> \x y -> f x y >> f y x
                              _ -> case ki of
                                     I -> f
                                     CoI -> flip f
      convPars Conv _ = convTest Conv
      convPars _    Pos = convTest Leq
      convPars _    Neg = flip (convTest Leq)
      convPars _    SPos = convTest Leq
      convPars _    Neut = convTest Conv
  convTest ct (App (Ind a1 b1 x1 ps1) ts1) (App (Ind a2 b2 x2 ps2) ts2)
    | x1 == x2 && b1 == b2 =
        do
          ind <- getGlobal x1
          traceTCM 70 $ text ("conv test " ++ show ct) <+> prettyTCM x1
                        <+>  text (show a1 ++ " ~~ " ++ show a2)
          addStageConstraints (mkConstraint (indKind ind) a1 a2)
          case ind of
            Inductive {} ->
                if length ts1 == length ts2
                then mAll (zipWith3 (convPars ct) (indPol ind) ps1 ps2) `mAnd`
                     mAll (zipWith (convTest Conv) ts1 ts2)
                else return False
            _ -> __IMPOSSIBLE__ -- sanity check
    | otherwise = return False
    where
      mkConstraint ki = case ct of
                         Conv -> (<<>>)
                         _ -> case ki of
                                I -> (<<=)
                                CoI -> flip (<<=)
      convPars Conv _ = convTest Conv
      convPars _    Pos = convTest Leq
      convPars _    Neg = flip (convTest Leq)
      convPars _    SPos = convTest Leq
      convPars _    Neut = convTest Conv

  convTest _ (Bound k1) (Bound k2) = return $ k1 == k2
  convTest _ (CBound k1 _) (CBound k2 _) = return $ k1 == k2
  convTest _ (Var x1) (Var x2) = return $ x1 == x2
  convTest _ t@(Lam _ _) u@(Lam _ _) =
    convTest Conv uctx tctx `mAnd` pushCtx tctx (convTest Conv t' u')
      where
        (tctx, t') = unLam t
        (uctx, u') = unLam u
  convTest _ (App f1 ts1) (App f2 ts2) = convTest Conv f1 f2 `mAnd`
                                         mAll (zipWith (convTest Conv) ts1 ts2)
  convTest _ (Constr c1 _ ps1) (Constr c2 _ ps2) =
    return (c1 == c2) `mAnd`
    mAll (zipWith (convTest Conv) ps1 ps2)
  convTest _ (Fix f1 b1 _) (Fix f2 b2 _) = return (b1 == b2) `mAnd`
                                           convTest Conv f1 f2
  convTest _ (Case c1) (Case c2) =
    convTest Conv (caseArg c1) (caseArg c2) `mAnd`
    convTest Conv (caseIndices c1) (caseIndices c2) `mAnd`
    mAll (zipWith (convTest Conv) (caseBranches c1) (caseBranches c2))
  convTest Conv (Intro _ t1) (Intro _ t2) = convTest Conv t1 t2
  convTest Conv (CoIntro _ _ t1) (CoIntro _ _ t2) = convTest Conv t1 t2
  convTest c t u = do
     traceTCM 20 $ hsep [ text "conversion"
                        , text (show c)
                        , text "failed:"
                        , prettyTCM t $$ text "and" $$ prettyTCM u ]
     return False

instance Conversion FixTerm where
  convTest _ (FixTerm k1 n1 f1 stage1 ctx1 tp1 body1) (FixTerm k2 n2 f2 stage2 ctx2 tp2 body2) =
    return (k1 == k2) `mAnd`
    return (f1 == f2) `mAnd`
    return (n1 == n2) `mAnd`
    convTest Conv ctx1 ctx2 `mAnd`
    convTest Conv tp1 tp2 `mAnd`
    -- convTest Conv (eraseSizeCtx ctx1) (eraseSizeCtx ctx2) `mAnd`
    -- convTest Conv (eraseSize tp1) (eraseSize tp2) `mAnd`
    pushBind (mkBind f1 (mkPi ctx1 tp1)) (convTest Conv body1 body2)


instance Conversion a => Conversion (Arg a) where
  convTest ct arg1 arg2 = convTest ct (unArg arg1) (unArg arg2)

instance Conversion Bind where
  convTest ct b1 b2 =
    convTest ct (bindType b1) (bindType b2) `mAnd`
    convTest Conv (bindDef b1) (bindDef b2)


instance Conversion Context where
  convTest _ CtxEmpty CtxEmpty = return True
  convTest ct (b1 :> c1) (b2 :> c2) =
    convTest ct b1 b2 `mAnd` pushBind b1 (convTest ct c1 c2)
  convTest _ _ _ = return False

instance Conversion a => Conversion (Named a) where
  convTest ct x1 x2 = convTest ct (namedValue x1) (namedValue x2)


instance Conversion IndicesSpec where
  convTest Conv (IndicesSpec args1) (IndicesSpec args2) =
    mAll (zipWith (convTest Conv) args1 args2)

instance Conversion SinglePattern where
  convTest Conv (PatternDef _ t1) (PatternDef _ t2) = convTest Conv t1 t2
  convTest Conv (PatternVar _) (PatternVar _) = return True
  convTest Conv _ _ = return False



-- TODO: check if we need to compare substs. See also CICwf.TypeChecking.Whnf
instance Conversion Branch where
  convTest Conv (Branch sv1 nm1 _ _ body1) (Branch sv2 nm2 _ _ body2) =
    return (sv1 == sv2 && nm1 == nm2) `mAnd`
    convTest Conv body1 body2
