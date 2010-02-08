{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes
  #-}

module Kernel.TCM where

import qualified Control.Exception as E

import Data.Typeable

import "mtl" Control.Monad.Reader

import Syntax.Internal hiding (lift)
import Syntax.ETag
import Environment
import Utils.MonadUndo

-- Type checking

data TypeError 
    = NotConvertible (Term NM) (Term NM)
    | NotFunction (Term NM)
    | NotSort (Term NM)
    | InvalidProductRule (Term NM) (Term NM)
    | IdentifierNotFound Name
    | ConstantError String
    deriving(Typeable,Show)

instance E.Exception TypeError


type TCState = GlobalEnv NM
type TCEnv = [Type NM]

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

lookupGlobal :: (MonadTCM tcm) => Name -> tcm (Global NM)
lookupGlobal x = do g <- lookupGE x 
                    case g of
                      Just t -> return t
                      Nothing -> typeError $ IdentifierNotFound x



