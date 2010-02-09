{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes
  #-}

module Refiner.RM where

import Data.Typeable

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import Control.Exception

import Syntax.Internal hiding (lift)
import Syntax.Global
import qualified Syntax.Abstract as A
import Utils.Fresh
import Environment

-- Refiner error

data RefinerError 
    = RefinerError String
    deriving(Typeable,Show)

instance Exception RefinerError

data Goal = Goal { goalCxt :: ENamedCxt,
                   goalType :: EType }
            -- deriving(Show)

instance Show Goal where
    show (Goal c t) = s ++ "\n------------\n" ++ A.ppExpr (map bind c) (reify t)
        where (s,_) = foldr (\g (s,e) -> (s++ "\n" ++ (bind g) ++ ":" ++ A.ppExpr e (reify (expr g)), (bind g):e)) ("",[]) c

showGoalType :: Goal -> String
showGoalType (Goal c t) = A.ppExpr (map bind c) (reify t)

class (Monad m) => HasGoal m where
    addGoal :: MetaId -> Goal -> m ()
    removeGoal :: MetaId -> m ()
    mapGoal :: (Goal -> Goal) -> m ()

class (MonadIO m,
       MonadGE m,
       HasGoal m,
       Functor m,
       MonadReader ENamedCxt m,
       Fresh MetaId m) => MonadRM m


refinerError :: (MonadRM rm) => RefinerError -> rm a
refinerError = liftIO . throwIO
        
lookupGlobal :: (MonadRM rm) => Name -> rm Global
lookupGlobal x = do g <- lookupGE x 
                    case g of
                      Just t -> return t
                      Nothing -> refinerError $ RefinerError "lookupGlobal"
