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

{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE PatternGuards  #-}

module CICwf.TypeChecking.TCM where

import           Control.Applicative
import           Control.Monad.Catch -- Control.Exception
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Maybe
import           Data.Typeable

import           CICwf.Syntax.Common
import qualified CICwf.Syntax.Internal           as I
import           CICwf.Syntax.Position
-- import           CICwf.Syntax.Size
import           CICwf.Utils.Fresh
import           CICwf.Utils.Pretty hiding((<$>))
import           CICwf.Utils.Sized

import           CICwf.TypeChecking.Constraints  (CSet)
import qualified CICwf.TypeChecking.Constraints  as CS

-- | Type-checking monad

-- Type checking errors
-- We include scope errors, so we have to catch only one type
data TypeError
    = NotConvertible I.Term I.Term
    | TypeNotConvertible I.Term I.Type I.Type
    | NotFunction I.Term I.Type
    | NotSort I.Term I.Type
    | NotArity I.Term I.Type
    | NotConstructor I.Term
    | InvalidProductRule Sort Sort
    | CannotInferMeta
    | BranchPatternCannotMatch I.Term I.Term
    | BranchPatternNotConvertible I.Context I.Context
    -- Unification
    | NotUnifiable [(I.Term, I.SinglePattern)]
    | NotImpossibleBranch
    | NotImplemented String
    | GenericError String
    -- Scope checking
    | WrongNumberOfArguments Name Int Int
    | WrongFixNumber Name Int
    | UndefinedName Name
    | NotInductive Name
    | ConstructorNotApplied Name
    | InductiveNotApplied Name
    | PatternNotConstructor Name
    | FixRecursiveArgumentNotPositive
    | AlreadyDefined Name
    | InvalidStageAnnotation
    deriving(Show,Typeable)


-- instance Show TypeError where
--     show (NotConvertible t1 t2) = "NotConvertible"
    -- show (TypeNotConvertible t u1 u2) = "NotConvertible " ++ show r
    -- show (NotFunction r e t1) = "NotFunction " ++ show r
    -- show (NotSort r e t1) = "NotSort " ++ show r
    -- show (NotArity r t) = "NotArity " ++ show r
    -- show (InvalidProductRule r s1 s2) = "InvalidProductRule " ++ show r
    -- show (IdentifierNotFound r x) = "IdentifierNotFound " ++ show x ++ " " ++ show r
    -- show (ConstantError s) = "ConstantError " ++ s
    -- show (CannotInferMeta r) = "CannotInferMeta " ++ show r
    -- show (WrongNumberOfArguments r _ _ _) = "WrongNumberOfArguments " ++ show r
    -- show (WrongFixNumber r _ _) = "WrongFixNumber " ++ show r
    -- show (UndefinedName r x) = "UndefinedName " ++ show r ++ ": " ++ show x
    -- show (NotInductive r n) = "NotInductive " ++ show r ++ " " ++ show n
    -- show (ConstructorNotApplied r n) = "ConstructorNotApplied " ++ show r ++ " " ++ show n
    -- show (InductiveNotApplied r n) = "InductiveNotApplied " ++ show r ++ " " ++ show n
    -- show (PatternNotConstructor n) = "PatternNotConstructor " ++ show n
    -- show (FixRecursiveArgumentNotPositive r) = "FixRecursiveArgumentNotPositive " ++ show r
    -- show (AlreadyDefined n) = "AlreadyDefined " ++ show n
    -- show (NotUnifiable n) = "NotUnifiable " ++ show n
    -- show (NotImpossibleBranch r) = "NotImpossibleBranch " ++ show r
    -- show (NotImplemented r s) = "Feature not implemented " ++ show r ++ " " ++ s
    -- show (BranchPatternCannotMatch r t1 t2) =
    --   "Cannot match branch pattern " ++ show r ++ " "
    --   ++ show t1 ++ " ~~ " ++ show t2
    -- show (BranchPatternNotConvertible r c1 c2) =
    --   "Branch pattern not compatible with matching " ++ show r
    --   ++ show c1 ++ " ~~ " ++ show c2


-- instance Exception TypeError


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
          , stSizeMap            :: [(Name, I.Annot)]
          , stGoals              :: Map I.MetaVar I.Goal
          , stActiveGoal         :: Maybe I.MetaVar
          , stConstraints        :: SizeConstraint
          , stVerbosityLevel     :: Verbosity
          , stSolveConstraints   :: Bool
          -- Well-founded sizes
          , stWfStages           :: [(I.StageVar, [I.Annot])]
          , stWfEnv              :: WfEnv
          , stSizeNames          :: [I.SizeName]
          , stWfConstraints      :: [WfConstraint]
          }

newtype SizeConstraint = SizeConstraint { unSC :: CSet StageNode Range }

instance Show SizeConstraint where
  show (SizeConstraint cs) = show nodes ++ " " ++ show constraints
    where
      nodes = CS.labNodes cs
      constraints = CS.toList cs

type Signature = Map Name I.Global

type LocalScope = Env Name

-- Well-founded sizes

type WfEnv = Env WfDeclaration

wfDom :: WfEnv -> [I.Annot]
wfDom = reverse . wfDom_
  where
    wfDom_ EnvEmpty = []
    wfDom_ (es :< WfDeclaration x _) = I.mkAnnot x : wfDom_ es

wfLookup :: WfEnv -> I.SizeName -> Maybe I.Annot
wfLookup EnvEmpty _ = Nothing
wfLookup (env :< WfDeclaration x a) y | x == y = Just a
                                      | otherwise = wfLookup env y

data WfDeclaration = WfDeclaration I.SizeName I.Annot

instance Show WfDeclaration where
  show (WfDeclaration x a) = "^" ++ show x ++ " ⊑ " ++ show a

instance Pretty WfDeclaration where
  pretty = text . show

instance I.HasAnnot WfDeclaration where
  modifySize f (WfDeclaration im a) = WfDeclaration im (I.modifySize f a)
  fAnnot (WfDeclaration _ a) = I.fAnnot a

data WfConstraint = WfConstraint WfEnv I.Annot I.Annot
                  | WfIndependent I.SizeName [I.Annot]
                  | WfCheckpoint WfEnv


instance Show WfConstraint where
  show (WfConstraint env a1 a2) = concat [ show env, " ⊢ "
                                         , show a1, " ⊑ ", show a2 ]
  show (WfIndependent v as) = show v ++ " ∉ " ++ show as
  show (WfCheckpoint env) = "CHECK " ++ show env

instance Pretty WfConstraint where
  pretty = text . show

freshSizeName :: (MonadTCM tcm) => I.SizeName -> tcm I.SizeName
freshSizeName x = do
  ns <- stSizeNames <$> get
  let fx = doFreshName ns (if isNull x then mkName "x" else x)
  modify $ \st -> st { stSizeNames = fx : stSizeNames st }
  return fx
    where
      doFreshName xs y | y `notElem` xs = y
                       | otherwise = trySuffix xs y (0 :: Int)
      trySuffix xs y n | addSuffix y n `notElem` xs = addSuffix y n
                       | otherwise = trySuffix xs y (n+1)
      addSuffix y n = modifyName (++ show n) y

addWfConstraint :: (MonadTCM tcm) => I.Annot -> I.Annot -> tcm ()
addWfConstraint a1 a2 | I.isInfty a2 = return ()
                      | a1 == a2 = return ()
                      | otherwise    = do
  wf <- stWfEnv <$> get
  let con = WfConstraint wf a1 a2
  modify $ \st -> st { stWfConstraints = con : stWfConstraints st }

addWfIndependent :: (MonadTCM tcm) => I.SizeName -> [I.Annot] -> tcm ()
addWfIndependent a1 as =
  modify $ \st -> st { stWfConstraints = WfIndependent a1 as
                                         : stWfConstraints st }


withWfEnv :: (MonadTCM tcm) => WfEnv -> tcm a -> tcm a
withWfEnv = localWfEnv . const

localWfEnv :: (MonadTCM tcm) => (WfEnv -> WfEnv) -> tcm a -> tcm a
localWfEnv f x = do
  old <- stWfEnv <$> get
  modify $ \st -> st { stWfEnv = f old }
  y <- x
  modify $ \st -> st { stWfEnv = old }
  return y

pushWfDecl :: (MonadTCM tcm) => I.SizeName -> I.Annot -> tcm a -> tcm a
pushWfDecl sv a = localWfEnv (\env -> env :< WfDeclaration sv a)


getWfConstraints :: (MonadTCM tcm) => tcm [WfConstraint]
getWfConstraints = stWfConstraints <$> get

setWfConstraints :: (MonadTCM tcm) => [WfConstraint] -> tcm ()
setWfConstraints cons = modify $ \st -> st { stWfConstraints = cons }

clearWfConstraints :: (MonadTCM tcm) => tcm ()
clearWfConstraints = setWfConstraints [] >> modify (\st -> st { stWfStages = [], stWfEnv = EnvEmpty })

wfSetCheckpoint :: (MonadTCM tcm) => tcm ()
wfSetCheckpoint = do
  st <- get
  put (st { stWfConstraints = WfCheckpoint (stWfEnv st) : stWfConstraints st })

wfDelCheckpoint :: (MonadTCM tcm) => tcm ()
wfDelCheckpoint = modify $ \st ->
  st { stWfConstraints = remCP (stWfConstraints st) }
  where
    remCP [] = []
    remCP (WfCheckpoint _ : xs) = xs
    remCP (x : xs) = x : remCP xs

-- Adds a wf declaration to every constraint up to the first checkpoint
-- (which is removed in the process)
wfAddDecl :: (MonadTCM tcm) => I.SizeName -> I.Annot -> tcm ()
wfAddDecl sv a = do
  con <- stWfConstraints <$> get
  let (before, env, after) = splitCP con []
      after' = WfConstraint env a I.infty : map (ammendConstraint env) after
  setWfConstraints (reverse after' ++ before)
  where
    splitCP :: [WfConstraint] -> [WfConstraint] -> ([WfConstraint], WfEnv, [WfConstraint])
    splitCP (WfCheckpoint env : cs) acc = (cs, env, acc)
    splitCP (c : cs) acc = splitCP cs (c : acc)

    ammendConstraint :: WfEnv -> WfConstraint -> WfConstraint
    ammendConstraint _    c@(WfIndependent _ _)    = c
    ammendConstraint env0 (WfConstraint env a1 a2) = WfConstraint env' a1 a2
      where
        (cs, ds) = envSplitAt (envLen env - envLen env0) env
        env' = cs :< WfDeclaration sv a `envCat` ds

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
                                          (unSC (stConstraints st)))
                     , stWfStages = (stage, I.infty : wfDom (stWfEnv st))
                                    : stWfStages st }
  return stage

freshConstrainedStage :: MonadTCM tcm => Range -> I.Annot -> tcm I.StageVar
freshConstrainedStage rg a | Just im <- I.nbase a = do
  ctxdom <- (wfDom . stWfEnv) <$> get
  let (_, _ : dom) = splitAtFirst (I.mkAnnot im) ctxdom
  stage <- fresh
  modify $ \st -> st { stConstraints =
                          SizeConstraint (CS.addNode (VarNode stage) rg
                                          (unSC (stConstraints st)))
                     , stWfStages = (stage, dom) : stWfStages st }
  return stage
  where
    splitAtFirst :: (Eq a) => a -> [a] -> ([a], [a])
    splitAtFirst _ [] = ([], [])
    splitAtFirst x (y:ys) | x == y = ([], y:ys)
                          | otherwise = (y : ys', ys'')
      where (ys', ys'') = splitAtFirst x ys

-- Local environment
type TCEnv = Env I.Bind

localLength :: (MonadTCM tcm) => tcm Int
localLength = liftM envLen ask

localGet :: (MonadTCM tcm) => Int -> tcm I.Bind
localGet k = liftM (`envGet` k) ask

localGetByName :: (MonadTCM tcm) => Name -> tcm (Int, I.Bind)
localGetByName x = liftM (envFindi ((==x) . I.bindName)) ask


-- | Errors

data TCErr
  = TypeError Range TCEnv TypeError
  | ScopeError Range TypeError -- TODO: split TypeError type
  deriving(Show,Typeable)

instance Exception TCErr

instance HasRange TCErr where
  range (TypeError r _ _) = r
  range (ScopeError r _) = r

typeError :: (MonadTCM tcm) => Range -> TypeError -> tcm a
typeError r t = do
  e <- ask
  throwM $ TypeError r e t

typeError' :: (MonadTCM tcm) => TypeError -> tcm a
typeError' = typeError noRange


notImplemented :: (MonadTCM tcm) => Range -> String -> tcm a
notImplemented r s = typeError r $ NotImplemented s

wrongArg :: (MonadTCM tcm) => Range -> Name -> Int -> Int -> tcm a
wrongArg r x m n = typeError r $ WrongNumberOfArguments x m n

inductiveNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
inductiveNotApplied r x = typeError r $ InductiveNotApplied x

failIfDefined :: (MonadTCM tcm) => Name -> tcm ()
failIfDefined x = isGlobal x >>= flip when (scopeError' (AlreadyDefined x))

scopeError :: (MonadTCM tcm) => Range -> TypeError -> tcm a
scopeError r t = throwM $ ScopeError r t

scopeError' :: (MonadTCM tcm) => TypeError -> tcm a
scopeError' t = throwM $ ScopeError noRange t

undefinedName :: (MonadTCM tcm) => Range -> Name -> tcm a
undefinedName r x = scopeError r $ UndefinedName x

class (Functor tcm,
       Applicative tcm,
       MonadReader TCEnv tcm,
       MonadState TCState tcm,
       MonadIO tcm,
       MonadThrow tcm) => MonadTCM tcm

type TCM = ReaderT TCEnv (StateT TCState IO) -- StateT TCState (ReaderT TCEnv IO)

instance MonadTCM TCM

-- | Running the type checking monad
runTCM :: TCM a -> TCM (Either TCErr a)
runTCM m = (Right <$> m) `catch` (return . Left)

runTCMIO :: TCM a -> IO (Either TCErr a)
runTCMIO m = (Right <$> runTCMIO' m) `catch` (return . Left)

runTCMIO' :: TCM a -> IO a
runTCMIO' m = liftM fst $ runStateT (runReaderT m initialTCEnv) initialTCState


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
          , stSolveConstraints   = True
          , stWfStages           = []
          , stWfEnv              = EnvEmpty
          , stSizeNames          = []
          , stWfConstraints      = []
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
pushCtx ctx = -- do ctx' <- freshenCtx ctx
                local (<:> ctx)


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


addSize :: (MonadTCM tcm) => Name -> I.Annot -> tcm ()
addSize x s = modify (\st -> st { stSizeMap = (x,s) : stSizeMap st })

clearSizeMap :: (MonadTCM tcm) => tcm ()
clearSizeMap = setSizeMap []

getSize :: (MonadTCM tcm) => Name -> tcm (Maybe I.Annot)
getSize x = stSizeMap <$> get >>= return . lookup x

getSizeMap :: (MonadTCM tcm) => tcm [(Name, I.Annot)]
getSizeMap = stSizeMap <$> get

setSizeMap :: (MonadTCM tcm) => [(Name, I.Annot)] -> tcm ()
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
addStageConstraints cts = return ()
  --                         do
  -- -- traceTCM 70 $ return $ text "*** Adding constraints:" <+> text (show cts)
  -- st <- get
  -- -- traceTCM 70 $ return $ text "*** to:" <+> text (show (stConstraints sssst))
  -- modify $
  --   \st -> st { stConstraints =
  --                  SizeConstraint (CS.addConstraints cts (unSC (stConstraints st))) }


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
  clearWfConstraints

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

getSolveConstraints :: (MonadTCM tcm) => tcm Bool
getSolveConstraints = stSolveConstraints <$> get

setSolveConstraints :: (MonadTCM tcm) => Bool -> tcm ()
setSolveConstraints b = do st <- get
                           put $ st { stSolveConstraints = b }



traceTCM :: (MonadTCM tcm) => Verbosity -> tcm Doc -> tcm ()
traceTCM n t = do k <- getVerbosity
                  d <- t
                  when (n <= k) $ liftIO $ print d

--- For testing
testTCM_ :: TCM a -> IO (Either TCErr a)
testTCM_ m = runTCMIO m'
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
                , I.constrArgs    = ctxSingle (I.unNamed (I.Ind I.Star False (mkName "nat") []))
                , I.constrRec     = [0]
                , I.constrIndices = []
                }
