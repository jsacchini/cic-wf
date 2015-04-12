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

{-# LANGUAGE TupleSections #-}

module CICwf.TypeChecking.Declaration (inferDecl) where

import           Control.Monad

import qualified CICwf.Syntax.Abstract           as A
import qualified CICwf.Syntax.AbstractToConcrete as AC
import           CICwf.Syntax.Colors
import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal           hiding (lift)
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.Constraints
import           CICwf.TypeChecking.Conversion
import           CICwf.TypeChecking.Fixpoint
import           CICwf.TypeChecking.Inductive    (inferInd)
import           CICwf.TypeChecking.PrettyTCM    hiding ((<>))
import qualified CICwf.TypeChecking.PrettyTCM    as PP ((<>))
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors
import           CICwf.TypeChecking.TypeChecking
import           CICwf.TypeChecking.Whnf
import           CICwf.TypeChecking.SolveWf

import           CICwf.Utils.Misc


prettyKeyword :: (MonadTCM tcm) => String -> tcm Doc
prettyKeyword s = text s >>= white

mkFreshStages :: (MonadTCM tcm) => Range -> [Name] -> tcm [(Name, StageVar)]
mkFreshStages _  []     = return []
mkFreshStages rg (x:xs) = do
  sta <- freshStage rg
  addWfConstraint (mkAnnot sta) infty
  addSize x (mkAnnot sta)
  sizeMap <- mkFreshStages rg xs
  return $ (x, sta) : sizeMap

outputTopLevel :: (MonadTCM tcm) => tcm Doc -> tcm ()
outputTopLevel d = printTCMLn (d PP.<> line)


inferDecl :: (MonadTCM tcm) =>  A.Declaration -> tcm ()
inferDecl (A.Definition _ nm (Just (A.ConstrExpr rg stas expType)) expBody) = do

  -- Reset constraint-related state
  resetConstraints

  -- Infer type using new size map
  sizeMap <- mkFreshStages rg stas
  traceTCM 40 $ text "new size map" <+> prettyTCM sizeMap

  (tp, s) <- allowSizes $ inferType expType

  -- Infer body forbidding annotations
  (body, bodyTp) <- forbidAnnot $ infer expBody

  -- Check that types are convertible
  unlessM (bodyTp `subType` tp)
    $ typeError (range expBody) $ NotConvertible tp bodyTp

  -- Check that constrained type is satisfiable
  -- Step 1: check that there is no negative cycle for each size variable
  forM_ sizeMap checkConstraint
  -- Step 2: check that there is no path between any pair of size variables
  forM_ (pairs sizeMap) checkIndependence

  let body0 = body -- toInfty body
      tp0   = tp -- toInftyBut stas tp
  solveWfConstraints
  mapM_ addGlobal [mkNamed nm Definition { defType = ConstrType stas tp0
                                         , defTerm = body0 }]

    where
      pairs :: [a] -> [(a,a)]
      pairs [] = []
      pairs (x:xs) = map (x,) xs ++ pairs xs

      checkConstraint :: (MonadTCM tcm) => (Name, StageVar) -> tcm ()
      checkConstraint (nmsize, s) = do
        constraints <- allConstraints
        case findNegCycle (VarNode s) (unSC constraints) of
          [] -> return ()
          _  -> notImplemented rg ("Size constraint not satisfied "
                                   ++ show nmsize)

      checkIndependence :: (MonadTCM tcm) =>
                           ((Name, StageVar), (Name, StageVar)) -> tcm ()
      checkIndependence ((nm1, s1), (nm2, s2)) =
        checkPath nm1 s1 s2 >> checkPath nm2 s2 s1

      checkPath :: (MonadTCM tcm) =>
                   Name -> StageVar -> StageVar -> tcm ()
      checkPath nmsize s1 s2 = do
        constraints <- allConstraints
        -- Check that there is no path from s1 to s2
        let ups = upward (unSC constraints) [VarNode s1]
        when (VarNode s2 `elem` ups)
          $ notImplemented rg ("Size constraint not satisfied "
                               ++ show nmsize)

inferDecl (A.Definition _ x Nothing e) = do
  resetConstraints
  (tm, tp) <- infer e
  let tm0 = tm -- toInfty tm
      tp0 = tp -- toInfty tp
  solveWfConstraints
  mapM_ addGlobal [mkNamed x Definition { defType = ConstrType [] tp0
                                        , defTerm = tm0 }]

inferDecl (A.Assumption rg nm (A.ConstrExpr _ stas expr)) = do
  resetConstraints
  _ {- sizeMap -} <- mkFreshStages rg stas
  (tm, tp) <- allowSizes $ inferType expr
  let tm0 = toInftyBut stas tm
  clearSizeMap
  mapM_ addGlobal [mkNamed nm (Assumption (ConstrType stas tm0))]

inferDecl (A.Inductive _ indDef) = do
  resetConstraints
  inferInd indDef >>= mapM_ addGlobal

inferDecl (A.Eval e) = do
  traceTCM 35 $ hsep [text "========= EVAL "]
  resetConstraints
  (e1, _) <- infer e
  let tm0 = e1 -- toInfty e1
  traceTCM 35 $ hsep [text "========= EVAL ", prettyTCM e1 PP.<> dot]
  tm1 <- nF tm0
  traceTCM 35 $ vcat [text "Normal form obtained ", prettyTCM tm1]
  outputTopLevel (prettyKeyword "eval"
                  <+> prettyTCM tm0 <+> text "="
                  $$ text "  " <+> prettyTCM tm1)

inferDecl (A.Check e1 (Just e2)) = do
  resetConstraints
  (tp, s) <- inferType e2
  tm <- check e1 tp
  let tm0 = tm -- toInfty tm
      tp0 = tp -- toInfty tp
  outputTopLevel $ vcat [ prettyKeyword "check" <+>
                          prettyTCM tm0
                        , text " : " PP.<> align (prettyTCM tp0) ]

inferDecl (A.Check e1 Nothing) = do
  resetConstraints
  (tm, tp) <- infer e1
  let tm0 = tm -- toInfty tm
      tp0 = tp -- toInfty tp
  outputTopLevel $ vcat [ prettyKeyword "check" <+>
                          prettyTCM tm0
                        , text " : " PP.<> align (prettyTCM tp0) ]

inferDecl (A.Print rg nm) = do
  resetConstraints
  g <- getGlobal nm
  case g of
    Definition ctype tm ->
      outputTopLevel (hsep [ prettyKeyword "define" <+>
                             prettyTCM nm, text ":", prettyTCM ctype ]
                      $$ text " = " PP.<> align (prettyTCM tm))
    Cofixpoint fix ctype ->
      outputTopLevel (prettyKeyword "fixpoint"
                      <+> prettyTCM fix
                      $$ text " : " PP.<> align (prettyTCM ctype))
    Assumption ctype ->
      outputTopLevel $ hsep [ prettyKeyword "assume"
                            , prettyTCM nm, text ":", prettyTCM ctype ]
    ind@Inductive {} ->
      outputTopLevel $ prettyTCM (mkNamed nm ind)
    constr@Constructor {} -> do
      ind@Inductive {} <- getGlobal (constrInd constr)
      outputTopLevel $ prettyTCM (mkNamed (constrInd constr) ind)


inferDecl (A.Cofixpoint fix) = do
  resetConstraints
  (fix', tp, ctype) <- inferFix fix
  let fix0 = fix' -- toInfty fix'
  solveWfConstraints
  addGlobal $
    mkNamed (A.fixName fix) Cofixpoint { cofixTerm = fix0
                                       , cofixType = ctype}
