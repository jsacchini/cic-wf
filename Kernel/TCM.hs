{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, DeriveDataTypeable,
    MultiParamTypeClasses, FlexibleInstances, UndecidableInstances
  #-}

module Kernel.TCM where

import Prelude hiding (catch)
import Control.Applicative
import Control.Exception
import Control.Monad

import Data.List
import qualified Data.Foldable as Fold
import Data.Typeable

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Graph.Inductive as GI

import Text.PrettyPrint

import Control.Monad.State
import Control.Monad.Reader

import qualified Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import Syntax.Size
import Utils.Fresh
import Utils.Pretty
import Utils.Sized

import Kernel.Constraints (CSet)
import qualified Kernel.Constraints as CS

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
    | UniverseInconsistency
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

type Verbosity = Int
-- Global state containing definition, assumption, datatypes, etc..
data TCState = TCState
               {
                 stSignature       :: Signature
               , stDefined         :: [Name] -- defined names in reverse order
               , stFresh           :: Fresh
               , stConstraints     :: CSet StageVar
               , stTypeConstraints :: CSet I.SortVar
               , stVerbosityLevel  :: Verbosity
               } deriving(Show)

type Signature = Map Name I.Global

-- Fresh
data Fresh = Fresh
             { freshStage :: StageVar
             , freshSort  :: I.SortVar }
             deriving(Show)

instance HasFresh StageVar Fresh where
  nextFresh f = (i, f { freshStage = succ i })
    where i = freshStage f

instance HasFresh I.SortVar Fresh where
  nextFresh f = (i, f { freshSort = succ i })
    where i = freshSort f

-- instance HasFresh i Fresh => HasFresh i TCState where
--   nextFresh s = (i, s { stFresh = f })
--     where (i, f) = nextFresh $ stFresh s

instance HasFresh StageVar TCState where
  nextFresh s = (i, s { stFresh = f
                      , stConstraints = CS.addNode i (stConstraints s) })
    where (i, f) = nextFresh $ stFresh s

instance HasFresh I.SortVar TCState where
  nextFresh s = (i, s { stFresh = f
                      , stTypeConstraints = CS.addNode i (stTypeConstraints s) })
    where (i, f) = nextFresh $ stFresh s

-- Local environment
newtype TCEnv = TCEnv { unEnv :: [I.Bind] }
                deriving (Show)

-- What combinator is this?
withEnv :: ([I.Bind] -> [I.Bind])-> TCEnv -> TCEnv
withEnv f (TCEnv x) = TCEnv (f x)

localLength :: (MonadTCM tcm) => tcm Int
localLength = liftM (length . unEnv) ask

localGet :: (MonadTCM tcm) => Int -> tcm I.Bind
localGet k = liftM ((!! k) . unEnv) ask

data TCErr = TCErr TypeError
             deriving(Show, Typeable)

instance Exception TCErr

class (Functor tcm,
       Applicative tcm,
       MonadReader TCEnv tcm,
       MonadState TCState tcm,
       MonadIO tcm) => MonadTCM tcm

type TCM = ReaderT TCEnv (StateT TCState IO) -- StateT TCState (ReaderT TCEnv IO)

instance MonadTCM TCM

-- | Running the type checking monad
runTCM :: TCM a -> IO (Either TCErr a)
runTCM m = (Right <$> runTCM' m) `catch` (return . Left)

-- runTCM' :: TCM a -> IO a
-- runTCM' m = liftM fst $ runReaderT (runStateT m initialTCState) initialTCEnv
runTCM' m = liftM fst $ runStateT (runReaderT m initialTCEnv) initialTCState


initialTCState :: TCState
initialTCState =
  TCState { stSignature = Map.empty -- initialSignature,
          , stDefined = []
          , stFresh = initialFresh
          , stConstraints     = CS.addNode inftyStageVar CS.empty
          , stTypeConstraints = CS.empty
          , stVerbosityLevel = 1
          }

-- | 'initialSignature' contains the definition of natural numbers as an
--   inductive type
initialSignature :: Signature
initialSignature = foldr (uncurry Map.insert) Map.empty
                   [(Id "nat", natInd),
                    (Id "O", natO),
                    (Id "S", natS)]

initialFresh :: Fresh
initialFresh = Fresh { freshStage = succ inftyStageVar -- inftyStageVar is mapped to ∞
                     , freshSort  = toEnum 0 }

initialTCEnv :: TCEnv
initialTCEnv = TCEnv []

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
pushCtx ctx = local (withEnv (reverse (Fold.toList ctx)++))

pushType :: (MonadTCM tcm) => I.Type -> tcm a -> tcm a
pushType tp = local (withEnv (I.bindNoName tp:))

pushBind :: (MonadTCM tcm) => I.Bind -> tcm a -> tcm a
pushBind b = local (withEnv (b:))

-- | Returns the number of parameters of an inductive type.
--   Assumes that the global declaration exists and that is an inductive type
numParam :: (MonadTCM tcm) => Name -> tcm Int
numParam x = (size . I.indPars) <$> getGlobal x


getLocalNames :: (MonadTCM tcm) => tcm [Name]
getLocalNames = map I.bindName . unEnv <$> ask

-- We don't need the real type of the binds for scope checking, just the names
-- Maybe should be moved to another place
fakeBinds :: (MonadTCM tcm, HasNames a) => a -> tcm b -> tcm b
fakeBinds b = local (withEnv (map mkBind (reverse (getNames b))++))
              where mkBind x = I.Bind x False (I.Sort I.Prop) Nothing

-- Constraints

-- class HasConstraints s a where
--   getCSet    :: s -> CSet a
--   modifyCSet :: (CSet a -> CSet a) -> s -> s

-- instance HasConstraints TCState StageVar where
--   getCSet        = stConstraints
--   modifyCSet f s = s { stConstraints = f (stConstraints s) }

-- instance HasConstraints TCState I.SortVar where
--   getCSet        = stTypeConstraints
--   modifyCSet f s = s { stTypeConstraints = f (stTypeConstraints s) }

-- addConstraints :: (Enum a, MonadState s m, HasConstraints s a) => [CS.Constraint a] -> m ()
-- addConstraints cts = do
--   st <- get
--   put (modifyCSet (CS.addConstraints cts) st)


addStageConstraints :: (MonadTCM tcm) => [CS.Constraint StageVar] -> tcm ()
addStageConstraints cts =
  modify $ \st -> st { stConstraints = CS.addConstraints cts (stConstraints st) }

addTypeConstraints :: (MonadTCM tcm) => [CS.Constraint I.SortVar] -> tcm ()
addTypeConstraints cts = do
  modify $ \st -> st { stTypeConstraints = CS.addConstraints cts (stTypeConstraints st) }
  tpConstr <- stTypeConstraints <$> get
  case find ((/= []) . flip CS.findNegCycle tpConstr) (CS.listNodes tpConstr) of
    Just _ -> throw UniverseInconsistency
    Nothing -> return ()
  traceTCM 30 $ return (hsep (text "Adding type constraints: " :
                              map (\(x,y,k) -> hsep [prettyPrint x,
                                                     if k == 0 then text "<=" else text "<",
                                                     prettyPrint y
                                                    ]) cts))



removeStages :: (MonadTCM tcm) => [StageVar] -> tcm ()
removeStages ans =
  modify $ \st -> st { stConstraints = CS.delNodes ans (stConstraints st) }

allStages :: (MonadTCM tcm) => tcm [StageVar]
allStages = (CS.listNodes . stConstraints) <$> get

allConstraints :: (MonadTCM tcm) => tcm (CSet StageVar)
allConstraints = stConstraints <$> get

newConstraints :: (MonadTCM tcm) => (CSet StageVar) -> tcm ()
newConstraints c = modify $ \st -> st { stConstraints = c }

--- For debugging

levelBug, levelDetail :: Verbosity
levelBug    = 1
levelDetail = 80

getVerbosity :: (MonadTCM tcm) => tcm Verbosity
getVerbosity = stVerbosityLevel <$> get

traceTCM :: (MonadTCM tcm) => Verbosity -> tcm Doc -> tcm ()
traceTCM n t = do k <- getVerbosity
                  d <- t
                  when (n <= k) $ liftIO $ print d

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
  I.Inductive { I.indKind    = I
              , I.indPars    = empCtx
              , I.indPol     = []
              , I.indIndices = empCtx
              , I.indSort    = I.Type 0
              , I.indConstr  = [Id "O", Id "S"]
              }

natO :: I.Global
natO =
  I.Constructor { I.constrInd     = Id "nat"
                , I.constrId      = 0
                , I.constrPars    = empCtx
                , I.constrArgs    = empCtx
                , I.constrRec     = []
                , I.constrIndices = []
                }

natS :: I.Global
natS =
  I.Constructor { I.constrInd     = Id "nat",
                  I.constrId      = 1,
                  I.constrPars    = empCtx,
                  I.constrArgs    = I.unNamed (I.Ind Empty (Id "nat")) <| empCtx,
                  I.constrRec     = [0],
                  I.constrIndices = [] }

