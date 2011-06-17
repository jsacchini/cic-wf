{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, DeriveDataTypeable,
    MultiParamTypeClasses, FlexibleInstances, UndecidableInstances
  #-}

module Kernel.TCM where

import Prelude hiding (catch)
import Control.Applicative
import Control.Exception

import qualified Data.Foldable as Fold
import Data.Typeable

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Graph.Inductive

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader

import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Syntax.Size
import Utils.Fresh
import Utils.Sized

import Kernel.Constraints

-- Type checking errors
-- We include scope errors, so we have to catch only one type
data TypeError
    = NotConvertible TCEnv I.Term I.Term
    | NotFunction TCEnv I.Term
    | NotSort TCEnv I.Term
    | NotArity Range I.Term
    | NotConstructor TCEnv I.Term
    | InvalidProductRule Sort Sort
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
    | AlreadyDefined Name
    -- Unification
    | NotUnifiable
    | NotImpossibleBranch
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
                 stFresh :: Fresh,
                 stStarStages :: [Int], -- list of stages assigned to position
                                        -- types
                 stConstraints :: ConstraintSet
               }
               deriving(Show)

type Signature = Map Name I.Global

-- Fresh
data Fresh = Fresh { freshStage :: Int }
             deriving(Show)

instance HasFresh Int Fresh where
  nextFresh f = (i, f { freshStage = i + 1 })
    where i = freshStage f

instance HasFresh i Fresh => HasFresh i TCState where
  nextFresh s = (i, s { stFresh = f })
    where (i, f) = nextFresh $ stFresh s

getFreshStage :: (MonadTCM tcm) => tcm Int
getFreshStage = do
  x <- fresh
  st <- get
  put $ st { stConstraints = insNode (x, ()) $ stConstraints st }
  return x

resetStarStages :: (MonadTCM tcm) => tcm ()
resetStarStages = do st <- get
                     put $ st { stStarStages = [] }

getStarStages :: (MonadTCM tcm) => tcm [Int]
getStarStages = stStarStages <$> get

addStarStage :: (MonadTCM tcm) => Int -> tcm ()
addStarStage k = do st <- get
                    put $ st { stStarStages = k : stStarStages st }

-- Local environment
type TCEnv = [I.Bind]

data TCErr = TCErr TypeError
             deriving(Show, Typeable)

instance Exception TCErr

class (Functor tcm,
       Applicative tcm,
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
initialTCState = TCState { stSignature = Map.empty, -- initialSignature,
                           stDefined = [],
                           stFresh = initialFresh,
                           stStarStages = [],
                           stConstraints = emptyConstraints
                         }


-- | 'initialSignature' contains the definition of natural numbers as an
--   inductive type
initialSignature :: Signature
initialSignature = foldr (uncurry Map.insert) Map.empty
                   [(Id "nat", natInd),
                    (Id "O", natO),
                    (Id "S", natS)]

initialFresh :: Fresh
initialFresh = Fresh { freshStage = 1 }  -- 0 is mapped to Infty

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
getSignature = stSignature <$> get

lookupGlobal :: (MonadTCM tcm) => Name -> tcm (Maybe I.Global)
lookupGlobal x = do sig <- getSignature
                    return $ Map.lookup x sig

isGlobal :: (MonadTCM tcm) => Name -> tcm Bool
isGlobal x = Map.member x <$> getSignature

checkIfDefined :: (MonadTCM tcm) => Name -> tcm ()
checkIfDefined x = isGlobal x >>= flip when (throw (AlreadyDefined x))


getGlobal :: (MonadTCM tcm) => Name -> tcm I.Global
getGlobal x = do sig <- getSignature
                 return $ sig Map.! x

-- TODO: check that the name is not already defined
--       Should be done before typechecking a declaration
addGlobal :: (MonadTCM tcm) => Name -> I.Global -> tcm ()
addGlobal x g = do st <- get
                   put $ st { stSignature = Map.insert x g (stSignature st),
                              stDefined = x : stDefined st
                            }

pushCtx :: (MonadTCM tcm) => I.Context -> tcm a -> tcm a
pushCtx ctx = local (reverse (Fold.toList ctx)++)

pushType :: (MonadTCM tcm) => I.Type -> tcm a -> tcm a
pushType tp = local (I.bindNoName tp:)

pushBind :: (MonadTCM tcm) => I.Bind -> tcm a -> tcm a
pushBind b = local (b:)

-- | Returns the number of parameters of an inductive type.
--   Assumes that the global declaration exists and that is an inductive type
numParam :: (MonadTCM tcm) => Name -> tcm Int
numParam x = (size . I.indPars) <$> getGlobal x


getLocalNames :: (MonadTCM tcm) => tcm [Name]
getLocalNames = map I.bindName <$> ask

-- We don't need the real type of the binds for scope checking, just the names
-- Maybe should be moved to another place
fakeBinds :: (MonadTCM tcm, HasNames a) => a -> tcm b -> tcm b
fakeBinds b = local (map (flip I.Bind (I.Sort Prop)) (reverse (getNames b))++)


-- Constraints

addConstraints :: (MonadTCM tcm) => [Constraint] -> tcm ()
addConstraints cts =
  do s <- get
     put $ s { stConstraints = addCts (stConstraints s)  }
     -- traceTCM_ ["adding constraints ", show cts]
   where addCts g = insEdges cts g

--- For debugging
traceTCM :: (MonadTCM tcm) => String -> tcm ()
traceTCM s = liftIO $ putStrLn $ "++ " ++ s ++ " ++"

traceTCM_ :: (MonadTCM tcm) => [String] -> tcm ()
traceTCM_ = traceTCM . concat


--- For testing
testTCM_ :: TCM a -> IO (Either TCErr a)
testTCM_ m = runTCM m'
  where m' = do addGlobal (Id "nat") natInd
                addGlobal (Id "O")   natO
                addGlobal (Id "S")   natS
                m


-- Initial signature
natInd :: I.Global
natInd =
  I.Inductive { I.indPars    = empCtx,
                I.indPol     = [],
                I.indIndices = empCtx,
                I.indSort    = Type 0,
                I.indConstr  = [Id "O", Id "S"] }
natO :: I.Global
natO =
  I.Constructor { I.constrInd     = Id "nat",
                  I.constrId      = 0,
                  I.constrPars    = empCtx,
                  I.constrArgs    = empCtx,
                  I.constrRec     = [],
                  I.constrIndices = [] }

natS :: I.Global
natS =
  I.Constructor { I.constrInd     = Id "nat",
                  I.constrId      = 1,
                  I.constrPars    = empCtx,
                  I.constrArgs    = I.Bind noName (I.Ind Empty (Id "nat")) <| empCtx,
                  I.constrRec     = [0],
                  I.constrIndices = [] }

