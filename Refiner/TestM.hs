{-# LANGUAGE PackageImports, MultiParamTypeClasses,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes
 #-}
module Refiner.TestM where

import Refiner.Refiner
import Syntax.Internal
import Refiner.RM
import Parser
import Text.ParserCombinators.Parsec

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

import Syntax.ETag
import Utils.Fresh
import Environment
import Utils.Fresh

unRight (Right x) = x

data RMState = RMState { global :: GlobalEnv NM,
                         freshMeta :: MetaId,
                         goals :: [(MetaId, Goal)]
                       }
--               deriving(Show)

instance Show RMState where
    show (RMState _ _ g) = show g -- show f

newtype RM a = RM { unRM :: StateT RMState
                             (ReaderT (NamedCxt EVAR) IO) a }
    deriving (Monad,
              MonadReader (NamedCxt EVAR),
              MonadState RMState)

-- instance MonadGE RM where
--     lookupGE x = do g <- get
--                     let g' = global g
--                     case lookupEnv x g' of
--                       Just t -> return t
-- --                      Nothing -> throwIO $ IdentifierNotFound x


instance BuildFresh Int RMState where
    nextFresh s = (i, s { freshMeta = i+1 })
                  where i = freshMeta s

instance HasGoal RM where
    getGoal = do s <- get
                 return $ goals s
    putGoal g = do s <- get
                   put $ s { goals = g }

instance MonadGE RM where
    lookupGE x = do g <- get
                    return $ lookupEnv x (global g)

instance MonadRM RM


runRM = flip runReaderT [] .
        flip runStateT (RMState { global = emptyEnv, freshMeta = 0, goals = [] }) .
        unRM


testRM = runRM . refine . unRight . runParser (parseExpr pIdentMeta) () "" 