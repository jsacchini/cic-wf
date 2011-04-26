{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, DeriveDataTypeable
  #-}
-- | Monad for scope checking

module Syntax.ScopeMonad where

import Prelude hiding (catch)

import Control.Monad.Reader
import Control.Monad.State
import Control.Exception

import qualified Data.Map as Map

import Data.Functor
import Data.Typeable

import Syntax.Common
import Syntax.Position
import qualified Syntax.Internal as I
import qualified Kernel.TCM as TCM
import Utils.Misc

type ScopeState = TCM.Signature

data ScopeEnv = SEnv { senvNames :: [Name],  -- ^ List of bound names
                       senvPosType :: Bool   -- ^ Whether we are checking a
                                             --   position type or not
                     } deriving(Show)

data ScopeError =
  WrongNumberOfArguments Range Name Int Int
  | WrongFixNumber Range Name Int
  | UndefinedName Range Name
  | NotInductive Name
  | ConstructorNotApplied Range Name
  | PatternNotConstructor Name
  | FixRecursiveArgumentNotPositive Range
  | AlreadyDefined Name
  deriving(Show, Typeable)

instance Exception ScopeError

class (Functor sm,
       MonadReader ScopeEnv sm,
       MonadState ScopeState sm,
       MonadIO sm) => ScopeMonad sm

type ScopeM = StateT ScopeState (ReaderT ScopeEnv IO)

instance ScopeMonad ScopeM

-- | Running the type scope monad
runScopeM :: ScopeM a -> TCM.TCM a
runScopeM m = StateT (\st -> ReaderT (\_ -> appSnd (const st) <$> run_ st m))
  where
    run_ s m = runReaderT (runStateT m (TCM.stSignature s)) initialScopeEnv


initialScopeState :: ScopeState
initialScopeState = Map.empty

initialScopeEnv :: ScopeEnv
initialScopeEnv = SEnv [] False


isGlobal :: (ScopeMonad sm) => Name -> sm Bool
isGlobal x = fmap (Map.member x) get


checkIfDefined :: (ScopeMonad sm) => Name -> sm ()
checkIfDefined x = isGlobal x >>= flip when (throw (AlreadyDefined x))

getLocalNames :: (ScopeMonad sm) => sm [Name]
getLocalNames = senvNames <$> ask

lookupGlobal :: (ScopeMonad sm) => Name -> sm (Maybe I.Global)
lookupGlobal x = do sig <- get
                    return $ Map.lookup x sig

getGlobal :: (ScopeMonad sm) => Name -> sm I.Global
getGlobal x = do sig <- get
                 return $ sig Map.! x

-- | fakeBinds for the ScopeMonad
fakeBinds :: (ScopeMonad sm, HasNames a) => a -> sm b -> sm b
fakeBinds b = local (\senv -> SEnv { senvNames = (reverse (getNames b)++
                                                  senvNames senv),
                                     senvPosType = senvPosType senv })


-- For testing the ScopeMonad.
testScopeM :: ScopeM a -> IO (Either TCM.TCErr a)
testScopeM m = (Right <$> testScopeM' m) `catch` (return . Left)

testScopeM' :: ScopeM a -> IO a
testScopeM' m = liftM fst $ runReaderT (runStateT m initialScopeState)
                initialScopeEnv

--- For debugging
traceSM :: (ScopeMonad sm) => String -> sm ()
traceSM = liftIO . putStr

traceSM_ :: (ScopeMonad sm) => [String] -> sm ()
traceSM_ = traceSM . concat
