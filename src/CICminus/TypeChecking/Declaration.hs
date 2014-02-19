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
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module CICminus.TypeChecking.Declaration (inferDecl) where

import           Control.Monad

import qualified CICminus.Syntax.Abstract           as A
import qualified CICminus.Syntax.InternalToAbstract as IA
import qualified CICminus.Syntax.AbstractToConcrete as AC
import           CICminus.Syntax.Colors
import           CICminus.Syntax.Common
import           CICminus.Syntax.Internal           hiding (lift)
import           CICminus.Syntax.Position
import           CICminus.TypeChecking.Constraints
import           CICminus.TypeChecking.Conversion
import           CICminus.TypeChecking.Fixpoint
import           CICminus.TypeChecking.Inductive    (inferInd)
import           CICminus.TypeChecking.PrettyTCM    hiding ((<>))
import qualified CICminus.TypeChecking.PrettyTCM    as PP ((<>))
import           CICminus.TypeChecking.TCM
import           CICminus.TypeChecking.TCMErrors
import           CICminus.TypeChecking.TypeChecking
import           CICminus.TypeChecking.Whnf
import           CICminus.Utils.Misc


prettyKeyword :: (MonadTCM tcm) => String -> tcm Doc
prettyKeyword s = text s >>= white

mkFreshStages :: (MonadTCM tcm) => Range -> [Name] -> tcm [(Name, StageVar)]
mkFreshStages _  []     = return []
mkFreshStages rg (x:xs) = do
  sta <- freshStage rg
  addSize x sta
  sizeMap <- mkFreshStages rg xs
  return $ (x, sta) : sizeMap


inferDecl :: (MonadTCM tcm) =>  A.Declaration -> tcm ()
inferDecl (A.Definition _ nm (Just (A.ConstrExpr rg stas expType)) expBody) = do

  -- Reset constraint-related state
  resetConstraints

  -- Infer type using new size map
  sizeMap <- mkFreshStages rg stas
  traceTCM 40 $ text "new size map" <+> prettyTCM sizeMap

  (tp, s) <- allowSizes $ infer expType

  -- Check that its type is a sort
  _ <- isSort (range expType) s

  -- Infer body forbidding annotations
  (body, bodyTp) <- forbidAnnot $ infer expBody

  -- Check that types are convertible
  unlessM (bodyTp `subType` tp)
    $ throwNotConvertible (Just (range expBody)) tp bodyTp

  -- Check that constrained type is satisfiable
  -- Step 1: check that there is no negative cycle for each size variable
  forM_ sizeMap checkConstraint
  -- Step 2: check that there is no path between any pair of size variables
  forM_ (pairs sizeMap) checkIndependence

  let body0 = toInfty body
      tp0   = toInftyBut stas tp
  mapM_ addGlobal [mkNamed nm (Definition { defType = ConstrType stas tp0
                                          , defTerm = body0 })]

    where
      pairs :: [a] -> [(a,a)]
      pairs [] = []
      pairs (x:xs) = map ((x,)) xs ++ pairs xs

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
        if VarNode s2 `elem` ups
          then notImplemented rg ("Size constraint not satisfied "
                                  ++ show nmsize)
          else return ()

inferDecl (A.Definition _ x Nothing e) = do
  resetConstraints
  (tm, tp) <- infer e
  let tm0 = toInfty tm
      tp0 = toInfty tp
  mapM_ addGlobal [mkNamed x (Definition { defType = ConstrType [] tp0
                                         , defTerm = tm0 })]

inferDecl (A.Assumption rg nm (A.ConstrExpr _ stas expr)) = do
  resetConstraints
  _ {- sizeMap -} <- mkFreshStages rg stas
  (tm, tp) <- allowSizes $ infer expr
  let tm0 = toInftyBut stas tm
  clearSizeMap
  _ <- isSort rg tp
  mapM_ addGlobal [mkNamed nm (Assumption (ConstrType stas tm0))]

inferDecl (A.Inductive _ indDef) = do
  resetConstraints
  inferInd indDef >>= mapM_ addGlobal

inferDecl (A.Eval e) = do
  traceTCM 70 $ hsep [text "========= EVAL "]
  resetConstraints
  (e1, _) <- infer e
  let tm0 = toInfty e1
  traceTCM 70 $ hsep [text "========= EVAL ", prettyTCM e1 PP.<> dot]
  tm1 <- nF tm0
  traceTCM 70 $ vcat [text "Normal form obtained ", prettyTCM tm1]
  printTCMLn $ (prettyKeyword "eval"
                <+> prettyTCM tm0 <+> text "="
                $$ nest 4 (prettyTCM tm1))

inferDecl (A.Check e1 (Just e2)) = do
  resetConstraints
  (tp, s) <- infer e2
  _ <- isSort (range e2) s
  tm <- check e1 tp
  let tm0 = toInfty tm
      tp0 = toInfty tp
  ctm0 <- IA.reify tm0
  ctp0 <- IA.reify tp0
  traceTCM 5 $ hsep [ prettyKeyword "CHECK"
                    , text (show ctm0), text ":"
                    , text (show ctp0) ]
  printTCMLn $ vcat [ prettyKeyword "check" <+>
                      prettyTCM tm0
                    , nest 4 $ text ":" <+> prettyTCM tp0 ]

inferDecl (A.Check e1 Nothing) = do
  resetConstraints
  (tm, tp) <- infer e1
  let tm0 = toInfty tm
      tp0 = toInfty tp
  ctm0 <- IA.reify tm0
  ctp0 <- IA.reify tp0
  traceTCM 5 $ vcat [ prettyKeyword "CHECK"
                    , text (show ctm0), text ":"
                    , text (show ctp0) ]
  printTCMLn $ vcat [ prettyKeyword "check" <+>
                      prettyTCM tm0
                    , nest 4 $ text ":" <+> prettyTCM tp0 ]

inferDecl (A.Print rg nm) = do
  resetConstraints
  g <- getGlobal nm
  case g of
    Definition ctype tm ->
      printTCMLn (hsep [ prettyTCM nm, text "=", prettyTCM tm ]
                  $$ nest 4 (text ":" <+> prettyTCM ctype))
    Cofixpoint fix ctype ->
      printTCMLn $ (prettyKeyword "fixpoint"
                    <+> prettyTCM fix
                    $$ nest 4 (text ":" <+> prettyTCM ctype))
    Assumption ctype ->
      printTCMLn $ hsep [ prettyTCM nm, text ":", prettyTCM ctype ]
    ind@Inductive {} ->
      printTCMLn $ prettyTCM (mkNamed nm ind)
    constr@Constructor {} -> do
      ind@Inductive {} <- getGlobal (constrInd constr)
      printTCMLn $ prettyTCM (mkNamed (constrInd constr) ind)


inferDecl (A.Cofixpoint fix) = do
  resetConstraints
  (fix', tp, ctype) <- inferFix fix
  let fix0 = toInfty fix'
  addGlobal $
    mkNamed (A.fixName fix) (Cofixpoint { cofixTerm = fix0
                                        , cofixType = ctype})
