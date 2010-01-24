{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts 
  #-}

module TCM where

import "mtl" Control.Monad.Error
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State

import Internal hiding (lift)
import Environment

-- Type checking

data TCErr 
    = InternalError
    | NotConvertible Term Term
    | NotFunction Term
    | NotSort Term
    | InvalidProductRule Term Term
    | IdentifierNotFound Name
    deriving(Show)

instance Error TCErr where
    noMsg = InternalError

-- type Result a = Either TCErr a -- result of type checking and type inference

type TCState = GlobalEnv
type TCEnv = [Type]

newtype TCM m a = TCM { unTCM :: StateT TCState
                                 (ReaderT TCEnv
                                  (ErrorT TCErr m)) a }
    deriving (Monad,
              MonadState TCState,
              MonadReader TCEnv,
              MonadError TCErr)

-- newtype MonadTCM m a = MonadTCM { rrr :: ErrorT TCErr m a } -- result of type checking and type inference
--                        deriving(Monad, MonadError TCErr) 
-- type Result = MonadTCM Identity

type Result = TCM Identity

instance (Show a) => Show (Identity a) where
    show (Identity x) = show x

instance (Show a, Show b) => Show (ErrorT a Identity b) where
    show (ErrorT (Identity (Left e))) = "Error: " ++ show e
    show (ErrorT (Identity (Right t))) = show t

initialTCState :: TCState
initialTCState = emptyEnv

initialTCEnv :: TCEnv
initialTCEnv = []

runTCM :: TCState -> TCEnv -> Result a -> Either TCErr a
runTCM g l (TCM m) = runIdentity $ runErrorT $ runReaderT (mapReaderT (liftM fst) $ runStateT m g) l

runInitialTCM :: Result a -> Either TCErr a
runInitialTCM = runTCM initialTCState initialTCEnv

lookupGlobal :: Name -> Result Global
lookupGlobal x = do g <- get
                    case lookupEnv x g of
                      Just t -> return t
                      Nothing -> throwError $ IdentifierNotFound x

-- instance (Show a) => Show (Result a) where
--     show (MonadTCM x) = show x

--    show (Res (ErrorT (Identity (Left e)))) = "Error: " ++ show e
--    show (Res (ErrorT (Identity (Right t)))) = show t

