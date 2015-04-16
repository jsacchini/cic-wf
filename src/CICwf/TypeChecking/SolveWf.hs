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

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

module CICwf.TypeChecking.SolveWf where

import           Control.Monad.State


import           Data.Functor
import           Data.Integer.SAT             (Expr ((:+), (:-)),
                                               Prop ((:<=), (:>=)))
import qualified Data.Integer.SAT             as S
import           Data.List
import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as Map
import           Data.Maybe

import           CICwf.Syntax.Common
import           CICwf.Syntax.Internal
import           CICwf.Syntax.Position

import           CICwf.TypeChecking.PrettyTCM
import           CICwf.TypeChecking.TCM

import           CICwf.Utils.Misc


solveWfConstraints :: MonadTCM tcm => Range -> tcm [(StageVar, Annot)]
solveWfConstraints rg = do
  stages <- stWfStages <$> get
  cons <- getWfConstraints
  let stages' = stages -- map (appSnd (infty:)) stages
      prstages = foldr pruneIndependent stages' cons
      upinf = upwardInfty cons prstages
      prstages2 = pruneInfty upinf prstages
      downsize = downwardSize cons prstages2
      prstages3 = pruneSize downsize prstages2
      countOpts :: [(a,[b])] -> Integer
      countOpts = product . map (genericLength . snd)
  traceTCM 10 $ text "Stages: " <+> prettyTCM stages'
  traceTCM 10 $ text "Pruned: " <+> prettyTCM prstages
  traceTCM 10 $ text "Infty: " <+> prettyTCM (mustBeInfty prstages cons)
  traceTCM 10 $ text "upward graph:" <+> text (show (stageAdj (stageGraph cons)))
  traceTCM 10 $ text "upward infty: " <+> prettyTCM upinf
  traceTCM 10 $ text "Pruned infty: " <+> prettyTCM prstages2
  traceTCM 10 $ text "Bound: " <+> prettyTCM (mustBeNonInfty prstages2 cons)
  traceTCM 10 $ text "downward graph:" <+> text (show (stageAdj (revertGraph (stageGraph cons))))
  traceTCM 10 $ text "upward bound: " <+> prettyTCM downsize
  traceTCM 10 $ text "Pruned bound: " <+> prettyTCM prstages3
  traceTCM 10 $ text "Options: " <+> prettyTCM (countOpts stages') <+> prettyTCM (countOpts prstages) <+> prettyTCM (countOpts prstages2) <+> prettyTCM (countOpts prstages3)
  traceTCM 10 $ text "Constraints: " <+> vcat (map prettyTCM cons)
  -- mapM_ (`test` cons) (maps stages')
  -- case findMaybe (solve cons) (maps prstages3) of
  --   Just r -> traceTCM 10 (text "SOLVED: " <+> prettyTCM r) >> return r
  --   Nothing -> traceTCM 10 (text "NOSAT") >> typeError noRange (GenericError "NOSAT")
  ifM getSolveConstraints
    (do r0 <- if null prstages3 then return (Just [])
              else findTCM (length prstages3) (solve cons) (maps prstages3)
        case r0 of
          Just r -> traceTCM 10 (text "SOLVED: " <+> prettyTCM r) >> return r
          Nothing -> traceTCM 10 (text "NOSAT") >> typeError rg (GenericError "NOSAT"))
    (return [])
  where
    test :: MonadTCM tcm => [(StageVar, Annot)] -> [WfConstraint] -> tcm ()
    test m1 cons = do
      traceTCM 10 $ text "==================================="
      traceTCM 10 $ text "Map:" <+> prettyTCM m1
      traceTCM 10 $ text "Presburger:" <+> vcat (map prettyTCM eqs)
      traceTCM 10 $ text "Non-neg:" <+> prettyTCM nonneg
      traceTCM 10 $ text "checkSat:" <+> maybe (text "NOSAT")
        (\x -> text "SAT" <+> prettyTCM (rename x)) res
      where
        eqs = map (\x -> (x, genEq m1 x)) cons
        notinf = map fst $ filter (\(x,y) -> not (isInfty y)) m1
        nonneg = map (\x -> S.Var (S.toName (fromEnum x)) :>= S.K 0) notinf
        bot = S.assert S.PFalse S.noProps
        mkProb xs = foldr S.assert S.noProps (xs ++ nonneg)
        prob1 = maybe bot mkProb (allMaybe (genEq m1) cons)
        res = S.checkSat prob1
        rename :: [(Int, a)] -> [(StageVar, a)]
        rename = map (appFst toEnum)


    findTCM :: (MonadTCM tcm) => Int -> (a -> Maybe b) -> [a] -> tcm (Maybe b)
    findTCM _ _ [] = return Nothing
    findTCM n f (x : xs) | Just y <- f x = return (Just y)
                         | otherwise     = when False {- (n `mod` 10000 == 0) -} (liftIO (print (show n))) >> findTCM (n-1) f xs

    solve :: [WfConstraint] -> [(StageVar, Annot)] -> Maybe [(StageVar, Annot)]
    solve cons m1 = res >>= \m -> return (map (subst m) m1)
      where
        -- eqs = map (\x -> (x, genEq m1 x)) cons
        notinf = map fst $ filter (\(x,y) -> not (isInfty y)) m1
        nonneg = map (\x -> S.Var (S.toName (fromEnum x)) :>= S.K 0) notinf
        bot = S.assert S.PFalse S.noProps
        mkProb xs = foldr S.assert S.noProps (xs ++ nonneg)
        prob1 = maybe bot mkProb (allMaybe (genEq m1) cons)
        res = S.checkSat prob1
        subst m (x, a) | isInfty a = (x, a)
                       | otherwise = case lookup (fromEnum x) m of
                                       Just n -> (x, hatn (fromInteger n) a)
                                       Nothing -> (x, a)

    maps :: [(a, [b])] -> [[(a,b)]]
    maps [] = []
    maps [(x,ys)] = [ [(x, y)] | y <- ys ]
    maps ((x,ys) : zss) = [ (x, y) : zs | y <- ys, zs <- maps zss ]

    pruneIndependent :: WfConstraint -> [(StageVar, [Annot])] ->
                        [(StageVar, [Annot])]
    pruneIndependent (WfIndependent im as) m = m'
      where
        m' = map (\ (x, bs) -> if mkAnnot x `elem` as
                               then (x, mkAnnot im `delete` bs)
                               else (x, bs) ) m
    pruneIndependent _ m = m

    mustBeInfty :: [(StageVar, [Annot])] -> [WfConstraint] -> [StageVar]
    mustBeInfty m cons =
      map fst (filter (\(_, xs) -> xs == [infty]) m) ++
      mapMaybe inf cons
      where
        inf (WfConstraint _ a1 a2) | isInfty a1 = sbase a2
        inf _ = Nothing

    mustBeNonInfty :: [(StageVar, [Annot])] -> [WfConstraint] -> [StageVar]
    mustBeNonInfty m cons =
      map fst (filter (\(_, xs) -> infty `notElem` xs) m) ++
      mapMaybe sizeBounded cons
      where
        sizeBounded (WfConstraint _ a1 a2) | Just _ <- nbase a2 = sbase a1
        sizeBounded _ = Nothing

    stageEdge :: WfConstraint -> Maybe (StageVar, StageVar)
    stageEdge (WfIndependent _ _) = Nothing
    stageEdge (WfConstraint _ a1 a2) | Just s1 <- sbase a1
                                     , Just s2 <- sbase a2 = Just (s1, s2)
                                     | otherwise = Nothing

    stageGraph :: [WfConstraint] -> [(StageVar, StageVar)]
    stageGraph = mapMaybe stageEdge

    revertGraph :: [(StageVar, StageVar)] -> [(StageVar, StageVar)]
    revertGraph = map (\(x,y) -> (y,x))

    stageAdj :: [(StageVar, StageVar)] -> Map StageVar [StageVar]
    stageAdj = foldr (\ (s1, s2) m -> Map.insertWith (++) s1 [s2] m) Map.empty

    upward :: Map StageVar [StageVar] -> [StageVar] -> [StageVar]
    upward gr = up []
      where
        up xs [] = xs
        up xs (y : ys) | y `elem` xs = up xs ys
                       | otherwise   = up (y : xs)
                                       (Map.findWithDefault [] y gr ++ ys)

    upwardInfty :: [WfConstraint] -> [(StageVar, [Annot])] -> [StageVar]
    upwardInfty cons m = upward (stageAdj (stageGraph cons)) (mustBeInfty m cons)

    pruneInfty :: [StageVar] -> [(StageVar, [Annot])] -> [(StageVar, [Annot])]
    pruneInfty vs = map remInfty
      where
        remInfty b@(x, xs) | x `elem` vs = (x, [infty])
                           | otherwise   = b

    downwardSize :: [WfConstraint] -> [(StageVar, [Annot])] -> [StageVar]
    downwardSize cons m = upward (stageAdj (revertGraph (stageGraph cons)))
                          (mustBeNonInfty m cons)

    pruneSize :: [StageVar] -> [(StageVar, [Annot])] -> [(StageVar, [Annot])]
    pruneSize vs = map remInfty
      where
        remInfty b@(x, xs) | x `elem` vs = (x, xs \\ [infty])
                           | otherwise = b

    -- findPath m a1 a2 assumes a1 and a2 are ground and a2 is not infty
    findPath :: WfEnv -> [(StageVar, Annot)] -> Annot -> Annot -> Maybe [S.Expr]
    findPath _ _ a1 _ | isInfty a1 = Nothing
    findPath _ _ a1 a2 | Just x1 <- nbase a1
                       , Just x2 <- nbase a2
                       , x1 == x2            = return []
    findPath env m a1 a2 = do
      exps <- findPath env m (substStageVars m b1) a2
      let e = case b1 of
            Stage (StageVar x n) -> S.Var (S.toName (fromEnum x))
                                    :+ S.K (toInteger n)
            SizeVar _ n          -> S.K (toInteger n)
            _                    -> S.K 0
      return (e : exps)
      where
        Just im1 = nbase a1
        Just b1 = wfLookup env im1

    genEq :: [(StageVar, Annot)] -> WfConstraint -> Maybe S.Prop
    genEq m (WfIndependent im as) = if im `elem` as'
                                    then Nothing else Just S.PTrue
      where
        as' = mapMaybe (nbase . substStageVars m) as
    genEq m (WfConstraint env a1 a2) =
      case (substStageVars m a1, substStageVars m a2) of
        (_, a2') | isInfty a2' -> Just S.PTrue
        (a1', _) | isInfty a1' -> Nothing
        (a1', a2') ->
          case findPath env m a1' a2' of
            Just exps -> Just (foldr (:+) (S.K (- len)) exps
                               :<= getExp a2 :- getExp a1)
                         where len = toInteger (length exps)
            Nothing -> Nothing
      where
        env' = substStageVars m (envToList env)
        getExp (Stage (StageVar x n)) = S.Var (S.toName (fromEnum x))
                                        :+ S.K (toInteger n)
        getExp (SizeVar x n) = S.K $ toInteger n
