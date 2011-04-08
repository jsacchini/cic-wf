{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving,
  PackageImports, TypeSynonymInstances, MultiParamTypeClasses,
  FlexibleInstances, DeriveDataTypeable  #-}

module TopLevel.Monad where

import Prelude hiding (catch)
import Data.Char
import Data.List
import Data.Maybe
import Data.Typeable

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Applicative

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Error

import qualified Control.Exception as Exn

import System.Console.Haskeline
import System.IO

import Syntax.Abstract
import Syntax.Bind
import Syntax.Name
import qualified Syntax.Scope as S
import Syntax.Global
import Utils.MonadUndo
import Kernel.TCM
import Kernel.Command
import qualified Kernel.GlobalMonad as GM
import qualified Kernel.Whnf as W
import qualified Syntax.Internal as I
import qualified Kernel.TypeChecking as T
import qualified Environment as Env
import Utils.Fresh
import Utils.Misc
import Syntax.Parser

import qualified Refiner.RM as RM
import qualified Refiner.Refiner as R
import qualified Refiner.Unify as RU


-- | Interaction monad.

data TopLevelErr = TypeError TypeError
                 | RefinerError RM.RefinerError
                 | MyIOException Exn.IOException
                 | MyParsingError ParsingError
                 | ScopeError S.ScopeError
                 | CommandError GM.CommandError
                 | InternalError String
                 | UnknownGoal
                 | NoSelectedGoal
                 | NoProofMode
                 | UnfinishedProof
                 deriving(Typeable,Show)

-- instance Error TopLevelErr where
--     strMsg = InternalError

instance Exn.Exception TopLevelErr


data TLState = TLState { global :: Env.GlobalEnv,
                         freshMeta :: I.MetaId,
                         goal :: Maybe (Name, I.Type, I.Term),
                         subGoals :: Map.Map I.MetaId RM.Goal,
                         currentSubGoal :: Maybe (I.MetaId, RM.Goal)
                       }

newtype TLM a = TLM { unTLM :: UndoT TLState IO a }
                deriving (Monad,
                          Functor,
                          MonadUndo TLState,
                          MonadState TLState
                          )

deriving instance MonadException TLM

instance MonadIO TLM where
    liftIO m = TLM $ liftIO $ m
                     `Exn.catch` catchP
                     `Exn.catch` catchIO
                     `Exn.catch` catchT
                     `Exn.catch` catchR
                     `Exn.catch` catchS
                     `Exn.catch` catchC
             where catchP = Exn.throwIO . MyParsingError
                   catchIO = Exn.throwIO . MyIOException
                   catchT = Exn.throwIO . TypeError
                   catchR = Exn.throwIO . RefinerError
                   catchS = Exn.throwIO . ScopeError
                   catchC = Exn.throwIO . CommandError


instance MonadTCM (ReaderT TCEnv TLM)

instance LookupName Global TLM where
    lookupName x = do g <- get
                      return $ Env.lookupEnv x (global g)
    definedName x = do g <- get
                       return $ Env.bindedEnv x (global g)

instance ExtendName Global TLM where
    extendName x a = modify $ \g -> g { global = Env.extendEnv x a (global g) }

instance BuildFresh I.MetaId TLState where
    nextFresh s = (freshMeta s, s { freshMeta = freshMeta s + 1 })

instance RM.HasGoal (ReaderT (I.NamedCxt) TLM) where
    addGoal i g = modify $ \s -> s { subGoals = Map.insert i g (subGoals s) }
    removeGoal i = modify $ \s -> s { subGoals = Map.delete i (subGoals s) }
    mapGoal f = modify $ \s -> s { subGoals = Map.map f (subGoals s) }

instance RM.MonadRM (ReaderT (I.NamedCxt) TLM)

instance S.ScopeMonad (ReaderT [Name] TLM)

instance GM.TCGlobalMonad TLM

runTLM :: TLM a -> IO (Either TopLevelErr a)
runTLM m = (Right <$> runTLM' m) `Exn.catch` (return . Left)

runTLM' :: TLM a -> IO a
runTLM' = flip evalUndoT initialTLState . unTLM

initialTLState :: TLState
initialTLState = TLState { global = Env.emptyEnv,
                           freshMeta = 0,
                           goal = Nothing,
                           subGoals = Map.empty,
                           currentSubGoal = Nothing  }


-- Lifted operations from RM

refine :: I.NamedCxt -> Expr -> I.Term -> TLM I.Term
refine xs e t = flip runReaderT xs $ R.refine e t

refineSub :: I.NamedCxt -> Expr -> I.Term -> TLM I.Term
refineSub xs e t = flip runReaderT xs $ fmap fst $ R.check e t

-- operations on the monad

showGlobal :: TLM ()
showGlobal = do g <- fmap global get
                liftIO $ putStr $ showEnv $ reverse $ Env.listEnv g
    where showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
          showG (x, Def t u) = "let " ++ x ++ " : " ++ I.ppTerm [] t ++ " := " ++ I.ppTerm [] u
          showG (x, Axiom t) = "axiom " ++ x ++ " : " ++ I.ppTerm [] t
          showG (x, t) = x ++ " : " ++ show t


showProof :: TLM ()
showProof = do g <- fmap goal get
               case g of
                 Just (x, t, e) -> liftIO $ putStrLn $ concat ["goal ", x, " : ", I.ppTerm [] t, " := ", I.ppTerm [] e]
                 Nothing -> throwIO NoProofMode

showContext :: TLM ()
showContext = do csg <- fmap currentSubGoal get
                 case csg of
                   Just (i, g) -> liftIO $ print g
                   Nothing -> throwIO NoSelectedGoal

showGoals :: TLM ()
showGoals = do g <- fmap subGoals get
               curr <- fmap goal get
               when (isNothing curr) $ throwIO NoProofMode
               -- liftIO $ putStr $ show $ Map.toList g
               liftIO $ putStr $ Map.foldWithKey showG "" g
    where showG n sg r = concat [show n, " : ", RM.showGoalType sg, "\n", r]

clearGoals :: TLM ()
clearGoals = modify $ \s -> s { goal = Nothing,
                                subGoals = Map.empty,
                                currentSubGoal = Nothing,
                                freshMeta = 0 }


qed :: TLM ()
qed = do sg <- fmap subGoals get
         cg <- fmap currentSubGoal get
         when (not (Map.null sg) || isJust cg) $ throwIO UnfinishedProof
         Just (x, t, e) <- fmap goal get
         GM.check (I.reify e) t -- check shouldn't fail
         GM.addGlobal x (Def t e) -- there should be no meta in e
         clearGoals

execCommand :: String -> TLM ()
execCommand xs = do csg <- fmap currentSubGoal get
                    case csg of
                      Nothing -> do c <- runParser "<interactive>" parseTopLevelCommand xs
                                    checkCommand c
                      Just (n, RM.Goal cxt t) -> do e <- runParser "<interactive>" parseExpr xs
                                                    e1 <- GM.scopeSub (map bind cxt) e
                                                    e' <- refineSub cxt e1 t
                                                    cg <- fmap goal get
                                                    modify $ \s -> s { goal = fmap (\(x,t,e) -> (x,t,RU.apply [(n,e')] e)) cg,
                                                                       currentSubGoal = Nothing,
                                                                       subGoals = Map.delete n (subGoals s)
                                                                     }
                                                    setSomeSubGoal

readAndSetSubGoal :: String -> TLM ()
readAndSetSubGoal xs = do n <- return (read xs :: I.MetaId) `catch` h
                          setSubGoal n
    where h :: Exn.SomeException -> TLM I.MetaId
          h = const $ throwIO UnknownGoal

setSubGoal :: I.MetaId -> TLM ()
setSubGoal n = do sg <- fmap subGoals get
                  case Map.lookup n sg of
                    Just goal -> modify $ \s -> s { currentSubGoal = Just (n,goal) }
                    Nothing -> throwIO $ UnknownGoal

setSomeSubGoal :: TLM ()
setSomeSubGoal = do sg <- fmap subGoals get
                    when (not (Map.null sg)) $ setSubGoal (fst (Map.findMin sg))
