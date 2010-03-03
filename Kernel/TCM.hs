{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes, FunctionalDependencies
  #-}

module Kernel.TCM where

import qualified Control.Exception as E

import Data.List
import Data.Typeable

import "mtl" Control.Monad.Reader

import qualified Syntax.Abstract as A
import Syntax.Bind
import Syntax.Internal hiding (lift)
import Syntax.Name
import Syntax.Global
import Syntax.ETag
import Environment
import Utils.MonadUndo

-- Type checking

data TypeError
    = NotConvertible TCEnv Term Term
    | NotFunction TCEnv Term
    | NotSort TCEnv Term
    | InvalidProductRule Sort Sort
    | IdentifierNotFound Name
    | ConstantError String
    deriving(Typeable)

instance Show TypeError where
    show (NotConvertible e t1 t2) = "NotConvertible " ++ ppTerm (map bind e) t1 ++ " " ++ ppTerm (map bind e) t2
    show (NotFunction e t1) = "NotFunction " ++ ppTerm (map bind e) t1
    show (NotSort e t1) = "NotSort " ++ ppTerm (map bind e) t1
    show (InvalidProductRule s1 s2) = "InvalidProductRule " ++ show s1 ++ " " ++ show s2
    show (IdentifierNotFound x) = "IdentifierNotFound " ++ x
    show (ConstantError s) = "ConstantError " ++ s

instance E.Exception TypeError

type TCState = GlobalEnv
type TCEnv = [BindT]

class (Functor tcm,
       MonadIO tcm,
       MonadReader TCEnv tcm,
       LookupName Global tcm,
       ExtendName Global tcm) => MonadTCM tcm where

-- | Running the type checking monad
-- runTCM :: TCM a -> IO (Either TCErr a)
-- runTCM m = (Right <$> runTCM' m) `E.catch` (return . Left)

initialTCState :: TCState
initialTCState = emptyEnv

initialTCEnv :: TCEnv
initialTCEnv = []

typeError :: (MonadTCM tcm) => TypeError -> tcm a
typeError = liftIO . E.throwIO

throwNotConvertible :: (MonadTCM tcm) => Term -> Term -> tcm a
throwNotConvertible t u = do e <- ask
                             typeError $ NotConvertible e t u

throwNotFunction :: (MonadTCM tcm) => Term -> tcm a
throwNotFunction t = do e <- ask
                        typeError $ NotFunction e t

lookupGlobal :: (MonadTCM tcm) => Name -> tcm Global
lookupGlobal x = do g <- lookupName x
                    case g of
                      Just t -> return t
                      Nothing -> typeError $ IdentifierNotFound x
