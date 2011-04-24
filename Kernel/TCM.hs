{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses,
  DeriveDataTypeable, RankNTypes, FunctionalDependencies
  #-}

module Kernel.TCM where

import Prelude hiding (catch)
import Control.Exception


import Data.List
import Data.Typeable

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Applicative
import "mtl" Control.Monad.Reader

import qualified Syntax.Abstract as A
import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Utils.MonadUndo

-- Type checking errors
-- We include scope errors, so we have to catch only one type
data TypeError
    = NotConvertible TCEnv I.Term I.Term
    | NotFunction TCEnv I.Term
    | NotSort TCEnv I.Term
    | NotArity Range I.Term
    | NotConstructor TCEnv I.Term
    | InvalidProductRule I.Sort I.Sort
    | IdentifierNotFound Name
    | ConstantError String
    -- Scope checking
    | WrongNumberOfArguments Range Name Int Int
    | WrongFixNumber Range Name Int
    | UndefinedName Range Name
    | NotInductive Name
    | ConstructorNotApplied Range Name
    | PatternNotConstructor Name
    | FixRecursiveArgumentNotPositive Range
    deriving(Show, Typeable)

-- instance Show TypeError where
--     show (NotConvertible e t1 t2) = "NotConvertible " ++ ppTerm (map bind e) t1 ++ " =!= " ++ ppTerm (map bind e) t2
--     show (NotFunction e t1) = "NotFunction " ++ ppI.Term (map bind e) t1
--     show (NotSort e t1) = "NotSort " ++ ppI.Term (map bind e) t1
--     show (NotArity e t1) = "NotArity " ++ ppI.Term (map bind e) t1
--     show (InvalidProductRule s1 s2) = "InvalidProductRule " ++ show s1 ++ " " ++ show s2
--     show (IdentifierNotFound x) = "IdentifierNotFound " ++ x
--     show (ConstantError s) = "ConstantError " ++ s

instance Exception TypeError


-- Global state containing definition, assumption, datatypes, etc..
data TCState = TCState
               { stSignature :: Signature,
                 stDefined :: [Name], -- defined names in reverse order
                 stFresh :: Fresh
               }
               deriving(Show)

type Signature = Map Name I.Global
type Fresh = Int

-- Local environment
type TCEnv = [I.Bind]

data TCErr = TCErr TypeError
             deriving(Show, Typeable)

instance Exception TCErr

class (Functor tcm,
       MonadReader TCEnv tcm,
       MonadState TCState tcm,
       MonadIO tcm) => MonadTCM tcm

type TCM = StateT TCState (ReaderT TCEnv IO)

instance MonadTCM TCM

-- | Running the type checking monad
runTCM :: TCM a -> IO (Either TCErr a)
runTCM m = (Right <$> runTCM' m) `catch` (return . Left)

runTCM' :: TCM a -> IO a
runTCM' m = liftM fst $ runReaderT (runStateT m initialTCState) initialTCEnv

initialTCState :: TCState
initialTCState = TCState { stSignature = Map.empty,
                           stDefined = [],
                           stFresh = 0
                         }

initialTCEnv :: TCEnv
initialTCEnv = []

typeError :: (MonadTCM tcm) => TypeError -> tcm a
typeError = throw

throwNotConvertible :: (MonadTCM tcm) => I.Term -> I.Term -> tcm a
throwNotConvertible t u = do e <- ask
                             typeError $ NotConvertible e t u

throwNotFunction :: (MonadTCM tcm) => I.Term -> tcm a
throwNotFunction t = do e <- ask
                        typeError $ NotFunction e t

getSignature :: (MonadTCM tcm) => tcm Signature
getSignature = fmap stSignature get

lookupGlobal :: (MonadTCM tcm) => Name -> tcm (Maybe I.Global)
lookupGlobal x = do sig <- getSignature
                    return $ Map.lookup x sig

getGlobal :: (MonadTCM tcm) => Name -> tcm I.Global
getGlobal x = do sig <- getSignature
                 -- liftIO $ putStrLn $ "getGlobal " ++ x ++ " " ++ show sig
                 return $ sig Map.! x

-- TODO: check that the name is not already defined
--       Should be done before typechecking a declaration
addGlobal :: (MonadTCM tcm) => Name -> I.Global -> tcm ()
addGlobal x g = do st <- get
                   put $ st { stSignature = Map.insert x g (stSignature st),
                              stDefined = x : stDefined st
                            }

getLocalNames :: (MonadTCM tcm) => tcm [Name]
getLocalNames = fmap (map I.bindName) ask


--- For debugging
traceTCM :: (MonadTCM tcm) => String -> tcm ()
traceTCM = liftIO . putStr

traceTCM_ :: (MonadTCM tcm) => [String] -> tcm ()
traceTCM_ = traceTCM . concat


--- For testing
testTCM_ :: TCM a -> IO (Either TCErr a)
testTCM_ m = runTCM m'
  where m' = do addGlobal (Id "nat") natInd
                addGlobal (Id "O")   natO
                addGlobal (Id "S")   natS
                m

natInd =
  I.Inductive { I.indPars    = [],
                I.indIndices = [],
                I.indSort    = I.Type 0,
                I.indConstr  = [Id "O", Id "S"] }
natO =
  I.Constructor { I.constrInd     = Id "nat",
                  I.constrId      = 0,
                  I.constrPars    = [],
                  I.constrArgs    = [],
                  I.constrIndices = [] }

natS =
  I.Constructor { I.constrInd     = Id "nat",
                  I.constrId      = 1,
                  I.constrPars    = [],
                  I.constrArgs    = [I.Bind noName (I.Bound 0)],
                  I.constrIndices = [] }

