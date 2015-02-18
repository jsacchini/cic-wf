{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
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

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module CICminus.TypeChecking.TCM where

import           Control.Applicative
import           Control.Exception
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe
import           Data.Typeable

import           CICminus.Syntax.Common
import qualified CICminus.Syntax.Internal           as I
import           CICminus.Syntax.Position
-- import           CICminus.Syntax.Size
import           CICminus.Utils.Fresh
import           CICminus.Utils.Pretty hiding((<$>))
import           CICminus.Utils.Sized

import           CICminus.TypeChecking.Constraints  (CSet)
import qualified CICminus.TypeChecking.Constraints  as CS

-- Type checking errors
-- We include scope errors, so we have to catch only one type
data TypeError
    = NotConvertible (Maybe Range) TCEnv I.Term I.Term
    | NotFunction (Maybe Range) TCEnv I.Term
    | NotSort Range TCEnv I.Term
    | NotArity Range I.Term
    | NotConstructor TCEnv I.Term
    | InvalidProductRule (Maybe Range) Sort Sort
    | IdentifierNotFound (Maybe Range) Name
    | ConstantError String
    | CannotInferMeta Range
    | BranchPatternCannotMatch Range I.Term I.Term
    | BranchPatternNotConvertible Range I.Context I.Context
    -- Scope checking
    | WrongNumberOfArguments Range Name Int Int
    | WrongFixNumber Range Name Int
    | UndefinedName Range Name
    | NotInductive Range Name
    | ConstructorNotApplied Range Name
    | InductiveNotApplied Range Name
    | PatternNotConstructor Name
    | FixRecursiveArgumentNotPositive Range
    | AlreadyDefined Name
    | InvalidStageAnnotation Range
    -- Unification
    | NotUnifiable Int
    | NotImpossibleBranch Range
    | NotImplemented Range String
    deriving(Typeable)

instance Show TypeError where
    show (NotConvertible r e t1 t2) = "NotConvertible " ++ show r
    show (NotFunction r e t1) = "NotFunction " ++ show r
    show (NotSort r e t1) = "NotSort " ++ show r
    show (NotArity r t) = "NotArity " ++ show r
    show (InvalidProductRule r s1 s2) = "InvalidProductRule " ++ show r
    show (IdentifierNotFound r x) = "IdentifierNotFound " ++ show x ++ " " ++ show r
    show (ConstantError s) = "ConstantError " ++ s
    show (CannotInferMeta r) = "CannotInferMeta " ++ show r
    show (WrongNumberOfArguments r _ _ _) = "WrongNumberOfArguments " ++ show r
    show (WrongFixNumber r _ _) = "WrongFixNumber " ++ show r
    show (UndefinedName r x) = "UndefinedName " ++ show r ++ ": " ++ show x
    show (NotInductive r n) = "NotInductive " ++ show r ++ " " ++ show n
    show (ConstructorNotApplied r n) = "ConstructorNotApplied " ++ show r ++ " " ++ show n
    show (InductiveNotApplied r n) = "InductiveNotApplied " ++ show r ++ " " ++ show n
    show (PatternNotConstructor n) = "PatternNotConstructor " ++ show n
    show (FixRecursiveArgumentNotPositive r) = "FixRecursiveArgumentNotPositive " ++ show r
    show (AlreadyDefined n) = "AlreadyDefined " ++ show n
    show (NotUnifiable n) = "NotUnifiable " ++ show n
    show (NotImpossibleBranch r) = "NotImpossibleBranch " ++ show r
    show (NotImplemented r s) = "Feature not implemented " ++ show r ++ " " ++ s
    show (BranchPatternCannotMatch r t1 t2) =
      "Cannot match branch pattern " ++ show r ++ " "
      ++ show t1 ++ " ~~ " ++ show t2
    show (BranchPatternNotConvertible r c1 c2) =
      "Branch pattern not compatible with matching " ++ show r
      ++ show c1 ++ " ~~ " ++ show c2


instance Exception TypeError


data StageNode
  = VarNode I.StageVar
  | InftyNode
  deriving(Eq)

instance Show StageNode where
  show (VarNode i) = show i
  show (InftyNode) = "∞"

instance Enum StageNode where
  fromEnum InftyNode = 0
  fromEnum (VarNode s) = fromEnum s + 1
  toEnum 0 = InftyNode
  toEnum n = VarNode $ toEnum (n-1)

type Verbosity = Int

data AllowedAnnotations
  = NoAnnotationsAllowed
  | StarAllowed
  | FullSizeAllowed
  deriving(Eq,Show)

-- Global state containing definition, assumption, datatypes, etc..
data TCState =
  TCState { stSignature          :: Signature
          , stDefined            :: [Name] -- global defined names in reverse
                                           -- order
          , stFresh              :: Fresh
          , stScope              :: LocalScope
          , stSizeScope          :: LocalScope
          , stAllowedAnnotations :: AllowedAnnotations
          , stStarSizes          :: [I.StageVar]
          , stSizeMap            :: [(Name, I.StageVar)]
          , stGoals              :: Map I.MetaVar I.Goal
          , stActiveGoal         :: Maybe I.MetaVar
          , stConstraints        :: SizeConstraint
          , stVerbosityLevel     :: Verbosity
          }

newtype SizeConstraint = SizeConstraint { unSC :: (CSet StageNode Range) }

instance Show SizeConstraint where
  show (SizeConstraint cs) = show nodes ++ " " ++ show constraints
    where
      nodes = CS.labNodes cs
      constraints = CS.toList cs

type Signature = Map Name I.Global

type LocalScope = Env Name

-- Fresh
data Fresh =
  Fresh { freshStageVar :: I.StageVar
        , freshMetaVar  :: I.MetaVar
        } deriving(Show)

instance HasFresh I.StageVar Fresh where
  nextFresh f = (i, f { freshStageVar = succ i })
    where i = freshStageVar f

instance HasFresh I.MetaVar Fresh where
  nextFresh f = (i, f { freshMetaVar = succ i })
    where i = freshMetaVar f

-- instance HasFresh i Fresh => HasFresh i TCState where
--   nextFresh s = (i, s { stFresh = f })
--     where (i, f) = nextFresh $ stFresh s

instance HasFresh I.StageVar TCState where
  nextFresh s =
    (i, s { stFresh = f })
          -- , stConstraints =
          --   SizeConstraint (CS.addNode (VarNode i) (unSC (stConstraints s))) })
    where (i, f) = nextFresh $ stFresh s

instance HasFresh I.MetaVar TCState where
  nextFresh s = (i, s { stFresh = f })
    where (i, f) = nextFresh $ stFresh s

freshStage :: MonadTCM tcm => Range -> tcm I.StageVar
freshStage rg = do
  stage <- fresh
  modify $ \st -> st { stConstraints =
                          SizeConstraint (CS.addNode (VarNode stage) rg
                                          (unSC (stConstraints st))) }
  return stage


-- Local environment
type TCEnv = Env I.Bind

localLength :: (MonadTCM tcm) => tcm Int
localLength = liftM envLen ask

localGet :: (MonadTCM tcm) => Int -> tcm I.Bind
localGet k = liftM (`envGet` k) ask

localGetByName :: (MonadTCM tcm) => Name -> tcm (Int, I.Bind)
localGetByName x = liftM (envFindi ((==x) . I.bindName)) ask


data TCErr = TCErr TypeError
             deriving(Show,Typeable)

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

runTCM' :: TCM a -> IO a
runTCM' m = liftM fst $ runStateT (runReaderT m initialTCEnv) initialTCState


initialTCState :: TCState
initialTCState =
  TCState { stSignature          = initialSignature
          , stDefined            = []
          , stFresh              = initialFresh
          , stGoals              = Map.empty
          , stScope              = EnvEmpty
          , stSizeScope          = EnvEmpty
          , stAllowedAnnotations = NoAnnotationsAllowed
          , stStarSizes          = []
          , stSizeMap            = []
          , stActiveGoal         = Nothing
          , stConstraints        = SizeConstraint
                                   $ CS.addNode InftyNode noRange CS.empty
          , stVerbosityLevel     = 30
          }

-- | 'initialSignature' contains the definition of natural numbers as an
--   inductive type
initialSignature :: Signature
initialSignature = foldr (uncurry Map.insert) Map.empty
                   [(mkName "nat", natInd),
                    (mkName "O", natO),
                    (mkName "S", natS)]

initialFresh :: Fresh
initialFresh = Fresh { freshStageVar = 0 -- 0 is mapped to InftyNode
                     , freshMetaVar  = toEnum 0 }

initialTCEnv :: TCEnv
initialTCEnv = EnvEmpty

typeError :: (MonadTCM tcm) => TypeError -> tcm a
typeError = throw

throwNotFunction :: (MonadTCM tcm) => I.Term -> tcm a
throwNotFunction t = do e <- ask
                        typeError $ NotFunction Nothing e t

getSignature :: (MonadTCM tcm) => tcm [Named I.Global]
getSignature = (reverse . stDefined <$> get) >>= mapM mkGlobal
  where
    mkGlobal x = liftM (mkNamed x) (getGlobal x)

lookupGlobal :: (MonadTCM tcm) => Name -> tcm (Maybe I.Global)
lookupGlobal x = do sig <- stSignature <$> get
                    return $ Map.lookup x sig

isGlobal :: (MonadTCM tcm) => Name -> tcm Bool
isGlobal x = Map.member x . stSignature <$> get


getGlobal :: (MonadTCM tcm) => Name -> tcm I.Global
getGlobal x = (Map.! x) . stSignature <$> get


-- | addGlobal adds a global definition to the signature.
--   Checking that names are not repeated is handled by the scope checker
addGlobal :: (MonadTCM tcm) => Named I.Global -> tcm ()
addGlobal g = do st <- get
                 put $ st { stSignature = Map.insert x d (stSignature st)
                          , stDefined = x : stDefined st
                          }
  where
    x = nameTag g
    d = namedValue g

withCtx :: (MonadTCM tcm) => I.Context -> tcm a -> tcm a
withCtx ctx = local (const (ctxToEnv ctx))

withEnv :: (MonadTCM tcm) => TCEnv -> tcm a -> tcm a
withEnv = local . const

freshenName :: (MonadTCM tcm) => Name -> tcm Name
freshenName x = do
  xs <- getLocalNames
  return $ doFreshName xs (if isNull x then mkName "x" else x)
    where
      doFreshName xs y | y `notElem` xs = y
                       | otherwise = trySuffix xs y (0 :: Int)
      trySuffix xs y n | addSuffix y n `notElem` xs = addSuffix y n
                       | otherwise = trySuffix xs y (n+1)
      addSuffix y n = modifyName (++ show n) y


freshenCtx :: (MonadTCM tcm) => I.Context -> I.Term -> tcm I.Context
freshenCtx CtxEmpty _ = return CtxEmpty
freshenCtx (b :> bs) t
  | I.isFree 0 (I.Pi bs t) = do
    y <- freshenName (I.bindName b)
    let b' = b { I.bindName = y }
    bs' <- pushBind b' (freshenCtx bs t)
    return $ b' :> bs'
  | otherwise = do
    let b' = b { I.bindName = noName }
    bs' <- pushBind b' (freshenCtx bs t)
    return $ b' :> bs'


fillNames :: (MonadTCM tcm) => I.Context -> tcm I.Context
fillNames CtxEmpty = return CtxEmpty
fillNames (b :> bs)
  | isNull (I.bindName b) = do
    liftIO $ print ("--> " ++ show (I.bindName b))
    y <- freshenName (I.bindName b)
    let b' = b { I.bindName = y }
    bs' <- pushBind b' (fillNames bs)
    return $ b' :> bs'
  | otherwise = do
    bs' <- pushBind b (fillNames bs)
    return $ b :> bs'


pushType :: (MonadTCM tcm) => I.Type -> tcm a -> tcm a
pushType tp m = do x <- freshenName (mkName "x")
                   pushBind (I.mkBind x tp) m

-- pushBind :: (MonadTCM tcm) => I.Bind -> tcm a -> tcm a
-- pushBind b m = do x <- freshenName (I.bindName b)
--                   let b' = b { I.bindName = x }
--                   local (:< b') m
pushBind :: (MonadTCM tcm) => I.Bind -> tcm a -> tcm a
pushBind b = local (:< b)

-- TODO: it should not be necessary to freshen a context everytime
-- only freshening during scope checking should be enough
pushCtx :: (MonadTCM tcm) => I.Context -> tcm a -> tcm a
pushCtx ctx m = -- do ctx' <- freshenCtx ctx
                   local (<:> ctx) m


extendEnv :: (MonadTCM tcm) => I.Environment -> tcm a -> tcm a
extendEnv env = local (`envCat` env)


withAllow :: (MonadTCM tcm) => AllowedAnnotations -> tcm a -> tcm a
withAllow a m = do
  olda <- stAllowedAnnotations <$> get
  -- liftIO $ putStrLn ("Allowing: " ++ show a)
  modify (\st -> st { stAllowedAnnotations = a })
  x <- m
  modify (\st -> st { stAllowedAnnotations = olda })
  -- liftIO $ putStrLn ("Restored: " ++ show olda)
  return x

allowStar :: (MonadTCM tcm) => tcm a -> tcm a
allowStar = withAllow StarAllowed

allowSizes :: (MonadTCM tcm) => tcm a -> tcm a
allowSizes = withAllow FullSizeAllowed

forbidAnnot :: (MonadTCM tcm) => tcm a -> tcm a
forbidAnnot = withAllow NoAnnotationsAllowed

isStarAllowed :: (MonadTCM tcm) => tcm Bool
isStarAllowed = stAllowedAnnotations <$> get >>= return . (== StarAllowed)

isSizeAllowed :: (MonadTCM tcm) => tcm Bool
isSizeAllowed = stAllowedAnnotations <$> get >>= return . (== FullSizeAllowed)


addStarStageVar :: (MonadTCM tcm) => I.StageVar -> tcm ()
addStarStageVar s = modify (\st -> st { stStarSizes = s : stStarSizes st })

clearStarStageVar :: (MonadTCM tcm) => tcm ()
clearStarStageVar = setStarStageVar []

getStarStageVar :: (MonadTCM tcm) => tcm [I.StageVar]
getStarStageVar = stStarSizes <$> get

setStarStageVar :: (MonadTCM tcm) => [I.StageVar] -> tcm ()
setStarStageVar ss = modify (\st -> st { stStarSizes = ss })


addSize :: (MonadTCM tcm) => Name -> I.StageVar -> tcm ()
addSize x s = modify (\st -> st { stSizeMap = (x,s) : stSizeMap st })

clearSizeMap :: (MonadTCM tcm) => tcm ()
clearSizeMap = setSizeMap []

getSize :: (MonadTCM tcm) => Name -> tcm (Maybe I.StageVar)
getSize x = stSizeMap <$> get >>= return . lookup x

getSizeMap :: (MonadTCM tcm) => tcm [(Name, I.StageVar)]
getSizeMap = stSizeMap <$> get

setSizeMap :: (MonadTCM tcm) => [(Name, I.StageVar)] -> tcm ()
setSizeMap m = modify (\st -> st { stSizeMap = m })



-- | Returns the number of parameters of an inductive type.
--   Assumes that the global declaration exists and that is an inductive type
numParam :: (MonadTCM tcm) => Name -> tcm Int
numParam x = (size . I.indPars) <$> getGlobal x


getLocalNames :: (MonadTCM tcm) => tcm [Name]
getLocalNames = ask >>= return . name

-- -- We don't need the real type of the binds for scope checking, just the names
-- -- Maybe should be moved to another place
-- fakeBinds :: (MonadTCM tcm, HasNames a) => a -> tcm b -> tcm b
-- fakeBinds b = pushCtx (mkFakeCtx b)
--   where
--     mkFakeCtx = ctxFromList . map mkFakeBind . name
--     mkFakeBind x = I.mkBind x (I.Sort I.Prop)

fakeNames :: (MonadTCM tcm) => Name -> tcm a -> tcm a
fakeNames x = pushCtx $ ctxSingle (I.mkBind x (I.Sort Prop))

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


addStageConstraints :: (MonadTCM tcm) => [CS.Constraint StageNode] -> tcm ()
addStageConstraints cts = do
  -- traceTCM 70 $ return $ text "*** Adding constraints:" <+> text (show cts)
  sssst <- get
  -- traceTCM 70 $ return $ text "*** to:" <+> text (show (stConstraints sssst))
  modify $
    \st -> st { stConstraints =
                   SizeConstraint (CS.addConstraints cts (unSC (stConstraints st))) }


removeStages :: (MonadTCM tcm) => [StageNode] -> tcm ()
removeStages ans =
  modify
  $ \st -> st { stConstraints = SizeConstraint (CS.delNodes ans (unSC (stConstraints st))) }

allStages :: (MonadTCM tcm) => tcm [StageNode]
allStages = (CS.listNodes . unSC . stConstraints) <$> get

allConstraints :: (MonadTCM tcm) => tcm SizeConstraint
allConstraints = stConstraints <$> get

newConstraints :: (MonadTCM tcm) => SizeConstraint -> tcm ()
newConstraints c = modify $ \st -> st { stConstraints = c }

resetConstraints :: (MonadTCM tcm) => tcm ()
resetConstraints = do
  newConstraints
    (SizeConstraint (CS.addNode InftyNode noRange CS.empty))
  clearSizeMap
  clearStarStageVar


-- Goals

listGoals :: (MonadTCM tcm) => tcm [(I.MetaVar, I.Goal)]
listGoals = (filter (isNothing . I.goalTerm . snd) . Map.assocs . stGoals) <$> get

addGoal :: (MonadTCM tcm) => I.MetaVar -> I.Goal -> tcm ()
addGoal m g = do st <- get
                 put $ st { stGoals = Map.insert m g (stGoals st) }

setActiveGoal :: (MonadTCM tcm) => Maybe I.MetaVar -> tcm ()
setActiveGoal k = modify $ \st -> st { stActiveGoal = k }

giveTerm :: (MonadTCM tcm) => I.MetaVar -> I.Term -> tcm ()
giveTerm k t =
  modify $ \st -> st { stGoals = Map.adjust (\g -> g { I.goalTerm = Just t }) k (stGoals st) }

getActiveGoal :: (MonadTCM tcm) => tcm (Maybe (I.MetaVar, I.Goal))
getActiveGoal = do k <- stActiveGoal <$> get
                   case k of
                     Nothing -> return Nothing
                     Just k  -> getGoal k >>= \(Just g) -> return (Just (k, g))

getGoal :: (MonadTCM tcm) => I.MetaVar -> tcm (Maybe I.Goal)
getGoal k = (Map.lookup k . stGoals) <$> get

--- For debugging

levelBug, levelDetail :: Verbosity
levelBug    = 1
levelDetail = 80

getVerbosity :: (MonadTCM tcm) => tcm Verbosity
getVerbosity = stVerbosityLevel <$> get

setVerbosity :: (MonadTCM tcm) => Verbosity -> tcm ()
setVerbosity n = do st <- get
                    put $ st { stVerbosityLevel = n }

traceTCM :: (MonadTCM tcm) => Verbosity -> tcm Doc -> tcm ()
traceTCM n t = do k <- getVerbosity
                  d <- t
                  when (n <= k) $ liftIO $ print d

--- For testing
testTCM_ :: TCM a -> IO (Either TCErr a)
testTCM_ m = runTCM m'
  where m' = do addGlobal (mkNamed (mkName "nat") natInd)
                addGlobal (mkNamed (mkName "O")   natO)
                addGlobal (mkNamed (mkName "S")   natS)
                m


-- Initial signature
natInd :: I.Global
natInd =
  I.Inductive { I.indKind    = I
              , I.indPars    = ctxEmpty
              , I.indPol     = []
              , I.indIndices = ctxEmpty
              , I.indSort    = Type 0
              , I.indConstr  = [mkName "O", mkName "S"]
              }

natO :: I.Global
natO =
  I.Constructor { I.constrInd     = mkName "nat"
                , I.constrId      = 0
                , I.constrPars    = ctxEmpty
                , I.constrArgs    = ctxEmpty
                , I.constrRec     = []
                , I.constrIndices = []
                }

natS :: I.Global
natS =
  I.Constructor { I.constrInd     = mkName "nat"
                , I.constrId      = 1
                , I.constrPars    = ctxEmpty
                , I.constrArgs    = ctxSingle (I.unNamed (I.Ind I.Star (mkName "nat") []))
                , I.constrRec     = [0]
                , I.constrIndices = []
                }
