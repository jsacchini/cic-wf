{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts 
  #-}

module TCM where

import "mtl" Control.Monad.Error hiding (lift)
import qualified "mtl" Control.Monad.Error as EE
import "mtl" Control.Monad.Identity
import Internal

-- Type checking

data TCErr 
    = InternalError
    | NotConvertible Term Term
    | NotFunction Term
    | NotSort Term
    | InvalidProductRule Term Term
    deriving(Show)

instance Error TCErr where
    noMsg = InternalError

-- type Result a = Either TCErr a -- result of type checking and type inference

newtype MonadTCM m a = MonadTCM { rrr :: ErrorT TCErr m a } -- result of type checking and type inference
                       deriving(Monad, MonadError TCErr) 
type Result = MonadTCM Identity

instance (Show a) => Show (Identity a) where
    show (Identity x) = show x

instance (Show a, Show b) => Show (ErrorT a Identity b) where
    show (ErrorT (Identity (Left e))) = "Error: " ++ show e
    show (ErrorT (Identity (Right t))) = show t

instance (Show a) => Show (Result a) where
    show (MonadTCM x) = show x

--    show (Res (ErrorT (Identity (Left e)))) = "Error: " ++ show e
--    show (Res (ErrorT (Identity (Right t)))) = show t
