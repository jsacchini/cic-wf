{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes, StandaloneDeriving
  #-}

module TCM where

import Control.Applicative
import qualified Control.Exception as E

import Data.Typeable

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

import Internal hiding (lift)
import Environment
import MonadUndo

import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec

-- Type checking

data TypeError 
    = NotConvertible Term Term
    | NotFunction Term
    | NotSort Term
    | InvalidProductRule Term Term
    | IdentifierNotFound Name
    | ConstantError String
    deriving(Typeable,Show)

data TCErr = TypeError TypeError
           | IOException E.IOException
           | ParsingError ParseError
           | AlreadyDefined String
           | InternalError String
           deriving(Typeable,Show)

instance Error TCErr where
    strMsg = InternalError

deriving instance Typeable ParseError
instance E.Exception ParseError

instance E.Exception TypeError

instance E.Exception TCErr

{-
data TCState' = TCState' { global :: GlobalEnv, 
                           goal :: ETerm,
                           subgoals :: Local
                           }

-}

type TCState = GlobalEnv
type TCEnv = [Type]

newtype TCM a = TCM { unTCM :: UndoT TCState
                               (ReaderT TCEnv IO) a }
    deriving (Functor,
              MonadState TCState,
              MonadUndo TCState,
              MonadReader TCEnv)

instance MonadError TCErr TCM where
  throwError = liftIO . E.throwIO
  catchError m h = TCM $ UndoT $ StateT $ \s -> ReaderT $ \e ->
    runReaderT (runUndoT (unTCM m) (current s)) e
    `E.catch` \err -> runReaderT (runUndoT (unTCM (h err)) (current s)) e


-- We want a special monad implementation of fail.
instance Monad TCM where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail    = throwError . InternalError

instance MonadIO TCM where
  liftIO m = TCM $ liftIO $ m `E.catch` catchP `E.catch` catchIO
             where catchP :: ParseError -> IO a
                   catchP = E.throwIO . ParsingError
                   catchIO :: E.IOException -> IO a
                   catchIO = E.throwIO . IOException

-- | Running the type checking monad
runTCM :: TCM a -> IO (Either TCErr a)
runTCM m = (Right <$> runTCM' m) `E.catch` (return . Left)

runTCM' :: TCM a -> IO a
runTCM' = flip runReaderT initialTCEnv .
          flip evalUndoT initialTCState .
          unTCM

initialTCState :: TCState
initialTCState = emptyEnv

initialTCEnv :: TCEnv
initialTCEnv = []

typeError :: TypeError -> TCM a
typeError = throwError . TypeError


addGlobal :: Name -> Type -> Term -> TCM ()
addGlobal x t u = do g <- get
                     when (bindedEnv x g) (throwError $ AlreadyDefined x)
                     put (extendEnv x (Def t u) g)

addAxiom :: Name -> Type -> TCM ()
addAxiom x t = do g <- get
                  when (bindedEnv x g) (throwError $ AlreadyDefined x)
                  put (extendEnv x (Axiom t) g)

lookupGlobal :: Name -> TCM Global
lookupGlobal x = do g <- get
                    case lookupEnv x g of
                      Just t -> return t
                      Nothing -> typeError $ IdentifierNotFound x



