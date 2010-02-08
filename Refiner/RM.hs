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
import qualified Syntax.Abstract as A
import Syntax.ETag
import Utils.Fresh
import Environment

-- Refiner error

data RefinerError 
    = RefinerError
    deriving(Typeable,Show)

instance Exception RefinerError

data Goal = Goal { goalCxt :: NamedCxt EVAR,
                   goalType :: Type EVAR }
--            deriving(Show)

instance Show Goal where
    show (Goal c t) = s ++ "\n------------\n" ++ (show $ A.tprint 0 (map fst c) (reify t))
        where (s,_) = foldr (\(x,t) (s,e) -> (s++ "\n" ++ x ++ ":" ++ (show $ A.tprint 0 e (reify t)), x:e)) ("",[]) c

class (Monad m) => HasGoal m where
    getGoal :: m [(MetaId, Goal)]
    putGoal :: [(MetaId, Goal)] -> m ()

class (MonadGE m,
       HasGoal m,
       MonadReader (NamedCxt EVAR) m,
       Fresh MetaId m) => MonadRM m

addGoal :: (HasGoal m) => MetaId -> Goal -> m ()
addGoal i g = do gs <- getGoal
                 putGoal $ (i,g):gs

removeGoal :: (HasGoal m) => MetaId -> m ()
removeGoal i = do gs <- getGoal
                  putGoal $ filter ((/=i) . fst) gs

modifyGoals :: (HasGoal m) => (Goal -> Goal) -> m ()
modifyGoals f = do gs <- getGoal
                   putGoal $ map (\(i,x) -> (i, f x)) gs


refinerError :: (MonadRM rm) => RefinerError -> rm a
refinerError = throw
        
lookupGlobal :: (MonadRM rm) => Name -> rm (Global NM)
lookupGlobal x = do g <- lookupGE x 
                    case g of
                      Just t -> return t
                      Nothing -> refinerError RefinerError
