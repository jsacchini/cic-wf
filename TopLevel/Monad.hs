{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving,
  PackageImports, TypeSynonymInstances, MultiParamTypeClasses,
  FlexibleInstances, DeriveDataTypeable  #-}

module TopLevel.Monad where

import Prelude hiding (catch)
import Data.Char
import Data.Typeable

import Control.Applicative

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.IO

import Syntax.Abstract
import Utils.MonadUndo
import Kernel.TCM
import qualified Syntax.Internal as I
import Syntax.ETag
import qualified Kernel.TypeChecking as T
import qualified Environment as E
import Utils.Fresh

import qualified Refiner.RM as RM


addGlobal :: Name -> I.Type NM -> I.Term NM -> TLM ()
addGlobal x t u = do g <- get
                     let g' = global g
                     when (E.bindedEnv x g') (throwIO $ AlreadyDefined x)
                     put $ g { global = (E.extendEnv x (I.Def t u) g') }

addAxiom :: Name -> I.Type NM -> TLM ()
addAxiom x t = do g <- get
                  let g' = global g
                  when (E.bindedEnv x g') (throwIO $ AlreadyDefined x)
                  put $ g { global = (E.extendEnv x (I.Axiom t) g') }

data TCErr = TypeError TypeError
           | RefinerError RM.RefinerError
           | MyIOException E.IOException
           | MyParsingError ParseError
           | AlreadyDefined String
           | InternalError String
           deriving(Typeable,Show)

instance Error TCErr where
    strMsg = InternalError

instance E.Exception TCErr


-- | Interaction monad.

data TLState = TLState { global :: E.GlobalEnv NM,
                         freshMeta :: I.MetaId,
                         goal :: Maybe RM.Goal,
                         subgoals :: [(I.MetaId, RM.Goal)]
                       }

newtype TLM a = TLM { unTLM :: UndoT TLState IO a }
                deriving (Monad, 
                          Functor,
                          MonadUndo TLState,
                          MonadState TLState
                          )

deriving instance MonadException TLM

instance MonadIO TLM where
  liftIO m = TLM $ liftIO $ m `E.catch` catchIO `E.catch` catchT `E.catch` catchR
             where -- catchP :: ParseError -> IO a
                   -- catchP = E.throwIO . ParsingError
                   catchIO :: E.IOException -> IO a
                   catchIO = E.throwIO . MyIOException
                   catchT :: TypeError -> IO a
                   catchT = E.throwIO . TypeError
                   catchR :: RM.RefinerError -> IO a
                   catchR = E.throwIO . RefinerError


instance MonadTCM (ReaderT TCEnv TLM)

instance E.MonadGE (ReaderT r TLM) where
    lookupGE x = do g <- get
                    return $ E.lookupEnv x (global g)

instance BuildFresh I.MetaId TLState where
    nextFresh s = (freshMeta s, s { freshMeta = freshMeta s + 1 })

instance RM.HasGoal (ReaderT (I.NamedCxt EVAR) TLM) where
    getGoal = do s <- get
                 return $ subgoals s
    putGoal g = do s <- get
                   put $ s { subgoals = g }

instance RM.MonadRM (ReaderT (I.NamedCxt EVAR) TLM)

runTLM :: TLM a -> IO (Either TCErr a)
runTLM m = (Right <$> runTLM' m) `E.catch` (return . Left)

runTLM' :: TLM a -> IO a
runTLM' = -- flip runReaderT [] .
          flip evalUndoT initialTLState .
          unTLM

initialTLState :: TLState
initialTLState = TLState { global = E.emptyEnv, 
                           freshMeta = 0,
                           goal = Nothing,
                           subgoals = []
                         }


infer :: Expr -> TLM (I.Term NM)
infer = flip runReaderT [] . T.infer

check :: Expr -> I.Term NM -> TLM ()
check e = flip runReaderT [] . T.check e

isSort :: I.Term NM -> TLM ()
isSort = flip runReaderT [] . T.isSort

runParserTLM :: FilePath -> GenParser tok () a -> [tok] -> TLM a
runParserTLM f p s = liftIO $ case runParser p () f s of
                                Left e -> throwIO $ MyParsingError e
                                Right t -> return t

