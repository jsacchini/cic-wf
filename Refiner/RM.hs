{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes, StandaloneDeriving
  #-}

module Refiner.RM where

import Control.Applicative
import qualified Control.Exception as E

import Data.Typeable

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Writer
import "mtl" Control.Monad.State
import Control.Exception

import Refiner.Internal hiding (lift)
import Utils.Fresh
import Refiner.Environment

-- Refiner error

data RefinerError 
    = RefinerError
    deriving(Typeable,Show)

instance E.Exception RefinerError

data Goal = Goal { goalCxt :: [Type],
                   goalType :: Type }
            deriving(Show)

class (Monad m) => HasGoal m where
    getGoal :: m [(MetaId, Goal)]
    putGoal :: [(MetaId, Goal)] -> m ()

class (MonadGE m,
       HasGoal m,
       MonadReader [Term] m,
       MonadState s m,
       HasFresh MetaId s) => MonadRM s m

data RMState = RMState { global :: GlobalEnv,
                         freshMeta :: MetaId,
                         goals :: [(MetaId, Goal)]
                       }
--               deriving(Show)

instance Show RMState where
    show (RMState _ _ g) = show g -- show f

newtype RM a = RM { unRM :: StateT RMState
                             (ReaderT [Term] IO) a }
    deriving (Monad,
              MonadReader [Term],
              MonadState RMState)

instance MonadGE RM where
    lookupGE x = do g <- get
                    let g' = global g
                    case lookupEnv x g' of
                      Just t -> return t
--                      Nothing -> throwIO $ IdentifierNotFound x


instance HasFresh Int RMState where
    nextFresh s = (i, s { freshMeta = i+1 })
                  where i = freshMeta s

instance HasGoal RM where
    getGoal = do s <- get
                 return $ goals s
    putGoal g = do s <- get
                   put $ s { goals = g }

addGoal :: (HasGoal m) => MetaId -> Goal -> m ()
addGoal i g = do gs <- getGoal
                 putGoal $ (i,g):gs

removeGoal :: (HasGoal m) => MetaId -> m ()
removeGoal i = do gs <- getGoal
                  putGoal $ filter ((/=i) . fst) gs

modifyGoals :: (HasGoal m) => (Goal -> Goal) -> m ()
modifyGoals f = do gs <- getGoal
                   putGoal $ map (\(i,x) -> (i, f x)) gs

instance MonadRM RMState RM


refinerError :: (MonadRM s rm) => RefinerError -> rm a
refinerError = throw

runRM = flip runReaderT [] .
        flip runStateT (RMState { global = emptyEnv, freshMeta = 0, goals = [] }) .
        unRM
        
        