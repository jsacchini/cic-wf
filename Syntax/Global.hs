{-# LANGUAGE FlexibleContexts #-}
module Syntax.Global where

import Syntax.Bind
import Syntax.Internal
import Syntax.Name

{---
TODO:
 - pretty printing of Global (ppGlobal :: Name -> Global -> String)
---}

data Global
    = Def Type Term
    | IndDef NamedCxt NamedCxt Sort [Constr]
    | ConstrDef (Name, Int) NamedCxt NamedCxt Sort NamedCxt [Term]
    | Axiom Type
    deriving(Show)

data Constr = MkConstr {
      constrName :: Name,
      constrArg :: NamedCxt,
      constrType :: [Term]
    } deriving(Show)

-- class (Monad m) => MonadGE m where
--     lookupGE :: Name -> m (Maybe Global)
--     toListGE :: m [(Name, Global)]
--     extendGE :: Name -> Global -> m ()

isInd :: (LookupName Global m) => Name -> m Bool
isInd n = do x <- lookupName n
             case x of
               Just (IndDef _ _ _ _) -> return True
               _ -> return False

isConstr :: (LookupName Global m) => Name -> m Bool
isConstr n = do x <- lookupName n
                case x of
                  Just (ConstrDef _ _ _ _ _ _) -> return True
                  _ -> return False

paramsInd :: (LookupName Global m) => Name -> m Int
paramsInd x = do n <- lookupName x
                 case n of
                   Just (IndDef params _ _ _) -> return (cxtSize params)

argsInd :: (LookupName Global m) => Name -> m Int
argsInd x = do n <- lookupName x
               case n of
                 Just (IndDef _ args _ _) -> return (cxtSize args)

paramsConstr :: (LookupName Global m) => Name -> m Int
paramsConstr x = do n <- lookupName x
                    case n of
                      Just (ConstrDef _ params _ _ _ _) -> return (cxtSize params)

argsConstr :: (LookupName Global m) => Name -> m Int
argsConstr x = do n <- lookupName x
                  case n of
                    Just (ConstrDef _ _ _ _ args _) -> return (cxtSize args)
