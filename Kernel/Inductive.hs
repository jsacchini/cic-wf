{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses
  #-}

module Kernel.Inductive where

import Control.Monad.Reader

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import {-# SOURCE #-} Kernel.TypeChecking
import Utils.Misc

{---
TODO:
 - positivity check in constructors
---}

-- | Type-checks an inductive definition returning a list of global definitions
--   for the inductive type and the constructors
instance Infer A.InductiveDef [(Name, Global)] where
  infer ind@(A.InductiveDef name pars tp constrs) =
    do liftIO $ putStrLn $ "\n INDUCTIVE " ++ show ind
       (pars', _) <- infer pars
       liftIO $ putStrLn $ "\n PARS " ++ show pars'
       (tp', s2)  <- local (reverse pars'++) $ infer tp
       liftIO $ putStrLn $ "\n TYPE " ++ show tp'
       _          <- isSort s2
       (args, s3) <- isArity (getRange tp) tp'
       cs         <- mapM (local (reverse pars'++) . flip check (name, pars', args, s3)) constrs
       liftIO $ putStrLn $ "\n CONSTRUCTORS " ++ show cs
       return $ (name, Inductive pars' args s3 constrNames) : fillIds cs
         where fillIds cs = map (\(idConstr, (x, c)) -> (x, c { constrId = idConstr })) (zip [0..] cs)
               constrNames = map A.constrName constrs

-- | Checks that a type is an arity.
--   Code is ugly
isArity :: (MonadTCM tcm) => Range -> Type -> tcm ([Bind], Sort)
isArity _ t =
  do (bs1, t1) <- unfoldPi t
     case t1 of
       Sort s -> return (bs1, s)
       _      -> error "Not arity. replace by error in TCErr"


instance Infer A.Parameter ([I.Bind], Sort) where
  infer (A.Parameter _ names tp) =
    do (tp', s) <- infer tp
       s' <- isSort s
       return (mkBindsSameType (map fst names) tp', s')


instance Check A.Constructor (Name, [Bind], [Bind], Sort) (Name, Global) where
  check (A.Constructor _ name tp _)
        (nmInd, parsInd, indicesInd, sortInd) =
    do (tp', s) <- local (indBind:) $  infer tp
       s' <- isSort s
       unlessM (conversion sortInd s') $ error "Error in constructor. Make up value for TCErr"
       liftIO $ putStrLn $ "Constr checking: " ++ show tp ++ " --> " ++ show tp'
       (args, indices) <- local (indBind:) $ isConstrType nmInd numPars (subst (Ind nmInd) tp')
       return (name, Constructor nmInd 0 parsInd args indices)
                     -- id is filled elsewhere
      where numPars = length parsInd
            indType
              | length parsInd + length indicesInd == 0 = Sort sortInd
              | otherwise = Pi (parsInd ++ indicesInd) (Sort sortInd)
            indBind = Bind nmInd indType

-- TODO: check that inductive type are applied to the parameters in order
--       check polarities of arguments and strict positivity of the inductive
--       type
isConstrType :: (MonadTCM tcm) => Name -> Int -> Type -> tcm ([Bind], [Term])
isConstrType nmInd numPars tp =
  do (bs1, tp') <- unfoldPi tp
     tp1 <- whnf tp'
     case tp1 of
       App (Ind i) args -> do when (i /= nmInd) $ error "Not constructor 1"
                              return (bs1, drop numPars args)
       Ind i            -> do when (i /= nmInd) $ error "Not constructor 1'"
                              return (bs1, [])
       t'               -> error $ "Not constructor 2. Make up value in TCErr " ++ show t'
