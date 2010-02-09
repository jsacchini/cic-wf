{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes
  #-}

module Kernel.TCM where

import qualified Control.Exception as E

import Data.List
import Data.Typeable

import "mtl" Control.Monad.Reader

import Syntax.Internal hiding (lift)
import Syntax.Global
import Syntax.ETag
import Environment
import Utils.MonadUndo

-- Type checking

data TypeError 
    = NotConvertible Term Term
    | NotFunction Term
    | NotSort Term
    | InvalidProductRule Sort Sort
    | IdentifierNotFound Name
    | ConstantError String
    deriving(Typeable,Show)

instance E.Exception TypeError


type TCState = GlobalEnv
type TCEnv = [Bind]

newtype TCMT m a = TCM { unTCM :: UndoT TCState
                                  (ReaderT TCEnv m) a }
    deriving (Monad,
              MonadIO,
              Functor,
              MonadState TCState,
              MonadUndo TCState,
              MonadReader TCEnv)

type TCM = TCMT IO

class ( MonadIO tcm
      , MonadReader TCEnv tcm
      , MonadGE tcm
      ) => MonadTCM tcm where

-- | Running the type checking monad
-- runTCM :: TCM a -> IO (Either TCErr a)
-- runTCM m = (Right <$> runTCM' m) `E.catch` (return . Left)

initialTCState :: TCState
initialTCState = emptyEnv

initialTCEnv :: TCEnv
initialTCEnv = []

typeError :: (MonadTCM tcm) => TypeError -> tcm a
typeError = liftIO . E.throwIO

lookupGlobal :: (MonadTCM tcm) => Name -> tcm Global
lookupGlobal x = do g <- lookupGE x 
                    case g of
                      Just t -> return t
                      Nothing -> typeError $ IdentifierNotFound x

indexBind :: (MonadTCM tcm) => Name -> tcm (Maybe Int)
indexBind x = do l <- ask
                 return $ findIndex indexFunc l
    where indexFunc (NoBind _) = False
          indexFunc (Bind y _) = x == y

elemBind :: (MonadTCM tcm) => Name -> tcm (Maybe Bind)
elemBind x = do l <- ask
                return $ find findFunc l
    where findFunc (NoBind _) = False
          findFunc (Bind y _) = x == y
