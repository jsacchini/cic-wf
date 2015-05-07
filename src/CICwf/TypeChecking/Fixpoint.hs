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

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module CICwf.TypeChecking.Fixpoint where

import           CICwf.Utils.Impossible

import           Control.Monad.Reader

import           Data.List
import           Data.Maybe
import           Data.Set            (Set)
import qualified Data.Set            as Set

import qualified CICwf.Syntax.Abstract           as A
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           as I
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.Constraints
import           CICwf.TypeChecking.Whnf
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import           CICwf.TypeChecking.RecCheck
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors
import {-# SOURCE #-} CICwf.TypeChecking.TypeChecking
import CICwf.Utils.Sized


-- | checkCoFixpointBody 'f' 'T' 'G' 'U' 't' check the following judgment:
--  (f:T) G |- t : U    (G and U need to be lifted to account for f.
checkCoFixpointBody :: (MonadTCM tcm) => Name -> Type -> Context -> Type
                       -> A.Expr
                       -> tcm Term
checkCoFixpointBody f tpRec ctx tpRet body = do
  let ctx1   = lift0 1 ctx
      tpRet1 = I.lift 1 (size ctx) tpRet

  body' <- forbidAnnot $ pushBind (mkBind f tpRec)
           $ pushCtx ctx1 $ check body tpRet1

  return body'



inferFix :: (MonadTCM tcm) => A.FixExpr -> tcm (FixTerm, Type, ConstrType)
inferFix fixexpr@(A.FixExpr rg ki nmf (A.FixPosition nRec) args tp body) =
  typeError rg $ GenericError "Position types are not allowed."

inferFix fixexpr@(A.FixExpr rg I nmf
                  (A.FixStruct rgspec nRec) args tp body) =
  typeError rg $ GenericError "Structural recursion is not allowed."

------------------------------------------------
-- * fix f <i> Delta : T := t
------------------------------------------------

inferFix fixexpr@(A.FixExpr rg ki nmf
                  (A.FixStage rgsta stage nRec) args tp body) = do

  oldSizeMap <- getSizeMap
  allOld <- allStages -- all stages before typechecking fix

  alpha <- freshSizeName stage
  addSize stage (mkAnnot alpha)


  (argCtx, _) <- allowSizes $ pushWfDecl alpha infty $ inferBinds args
  (tp', s) <- allowSizes $ pushWfDecl alpha infty $ pushCtx argCtx $ inferType tp


  traceTCM 20 $ hsep [ text "Typechecked fixpoint type: "
                     , prettyTCM (mkPi argCtx tp')]

  let resType = subsetType alpha infty (mkPi argCtx tp')
  traceTCM 20 $ hsep [ text "Well-founded fixpoint type: "
                     , prettyTCM resType ]


  let argsAnnot = Set.delete (mkAnnot alpha) (fAnnot (mkPi argCtx tp'))
  addWfIndependent alpha (Set.elems argsAnnot)

  -- Well-founded return type
  let replRecStage jm s@(SizeVar im n) | alpha == im = hatn n (mkAnnot jm)
      replRecStage _  s                              = s

  jm <- freshSizeName (mkName "j")
  let wfret = modifySize (replRecStage jm) (mkPi argCtx tp')
      recType0 = subsetType jm (mkAnnot alpha) wfret
  traceTCM 20 $ hsep [ text "Well-founded return type: "
                     , prettyTCM recType0 ]
  -- recType <- applyPartialSol recType0
  let recType = recType0

  body' <- pushWfDecl alpha infty $ checkCoFixpointBody nmf recType argCtx tp' body

  addWfIndependent alpha (Set.elems (fAnnot body'))


  -- Find constrained type
  let eraseNotAlpha _ s = s

      ctype = UnConstrType (mkPi argCtx tp') -- ConstrType [stage] (modifySize (eraseNotAlpha (Stage Infty)) (mkPi argCtx tp'))


  -- Restore star stages
  setSizeMap oldSizeMap

  -- Final result
  return ( FixTerm ki nRec nmf (FixStage alpha)
           (modifySize (eraseNotAlpha Empty) argCtx) (modifySize (eraseNotAlpha Empty) tp')
           ({- eraseSize -} body')
         , resType -- mkPi argCtx tp'
         , UnConstrType resType )-- ctype )
