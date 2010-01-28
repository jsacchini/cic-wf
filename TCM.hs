{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes
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
import Parser --- REMOVE ??

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

instance E.Exception TypeError

instance E.Exception TCErr

-- type Result a = Either TCErr a -- result of type checking and type inference

type TCState = GlobalEnv
type TCEnv = [Type]

newtype TCM m a = TCM { unTCM :: StateT TCState
                                 (ReaderT TCEnv m) a }
    deriving (MonadState TCState,
              MonadReader TCEnv)

type Result = TCM IO

instance MonadTrans TCM where
    lift = TCM . lift . lift 

instance MonadIO m => Functor (TCM m) where
    fmap = liftM

instance MonadIO m => Applicative (TCM m) where
    pure = return
    (<*>) = ap

instance MonadError TCErr (TCM IO) where
  throwError = liftIO . E.throwIO
  catchError m h = TCM $ StateT $ \s -> ReaderT $ \e ->
    runReaderT (runStateT (unTCM m) s) e
    `E.catch` \err -> runReaderT (runStateT (unTCM (h err)) s) e


class ( MonadIO tcm
      , MonadReader TCEnv tcm
      , MonadState TCState tcm
      ) => MonadTCM tcm where
    liftTCM :: Result a -> tcm a


-- runrun2 :: GenParser Char () a 
--         -> String -> Result a
-- runrun2 p s = lift $ runrun p s `E.catch` f
--               where f :: ParseError -> IO a
--                     f _ = E.throwIO $ InternalError ""

mapTCMT :: (forall a. m a -> n a) -> TCM m a -> TCM n a
mapTCMT f = TCM . mapStateT (mapReaderT f) . unTCM

-- pureTCM :: Monad m => (TCState -> TCEnv -> a) -> TCM m a
-- pureTCM f = TCM $ StateT $ \s -> ReaderT $ \e -> return (f s e, s)

instance MonadIO m => MonadTCM (TCM m) where
    liftTCM = mapTCMT liftIO

instance (Error err, MonadTCM tcm) => MonadTCM (ErrorT err tcm) where
    liftTCM = lift . liftTCM

-- We want a special monad implementation of fail.
instance MonadIO m => Monad (TCM m) where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail    = liftTCM . throwError . InternalError

instance MonadIO m => MonadIO (TCM m) where
  liftIO m = TCM $ liftIO $ m `E.catch` catchP `E.catch` catchIO
             where catchP :: ParseError -> IO a
                   catchP = E.throwIO . ParsingError
                   catchIO :: E.IOException -> IO a
                   catchIO = E.throwIO . IOException

-- | Running the type checking monad
runTCM :: Result a -> IO (Either TCErr a)
runTCM m = (Right <$> runTCM' m) `E.catch` (return . Left)

runTCM' :: Monad m => TCM m a -> m a
runTCM' = flip runReaderT initialTCEnv .
          flip evalStateT initialTCState .
          unTCM

initialTCState :: TCState
initialTCState = emptyEnv

initialTCEnv :: TCEnv
initialTCEnv = []

typeError :: (MonadTCM tcm) => TypeError -> tcm a
typeError = liftTCM . throwError . TypeError


addGlobal :: (MonadTCM tcm) => Name -> Type -> Term -> tcm ()
addGlobal x t u = do g <- get
                     liftTCM $ when (bindedEnv x g) (throwError $ AlreadyDefined x)
                     put (extendEnv x (Def t u) g)

addAxiom :: (MonadTCM tcm) => Name -> Type -> tcm ()
addAxiom x t = do g <- get
                  liftTCM $ when (bindedEnv x g) (throwError $ AlreadyDefined x)
                  put (extendEnv x (Axiom t) g)

lookupGlobal :: Name -> Result Global
lookupGlobal x = do g <- get
                    case lookupEnv x g of
                      Just t -> return t
                      Nothing -> typeError $ IdentifierNotFound x



