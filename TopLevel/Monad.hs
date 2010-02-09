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

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.IO

import Syntax.Abstract
import qualified Syntax.Scope as S
import qualified Syntax.Global as GE
import Utils.MonadUndo
import Kernel.TCM
import qualified Kernel.Whnf as W
import qualified Syntax.Internal as I
import qualified Kernel.TypeChecking as T
import qualified Environment as E
import Utils.Fresh
import Utils.Misc
import Syntax.Parser

import qualified Refiner.RM as RM
import qualified Refiner.Refiner as R
import qualified Refiner.Unify as RU


-- | Interaction monad.

data TopLevelErr = TypeError TypeError
                 | RefinerError RM.RefinerError
                 | MyIOException E.IOException
                 | MyParsingError ParseError
                 | AlreadyDefined String
                 | InternalError String
                 | UnknownGoal
                 | NoSelectedGoal
                 | NoProofMode
                 | UnfinishedProof
                 deriving(Typeable,Show)

instance Error TopLevelErr where
    strMsg = InternalError

instance E.Exception TopLevelErr


data TLState = TLState { global :: E.GlobalEnv,
                         freshMeta :: I.MetaId,
                         goal :: Maybe (Name, I.Type, I.ETerm),
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

instance GE.MonadGE (ReaderT r TLM) where
    lookupGE x = do g <- get
                    return $ E.lookupEnv x (global g)

instance BuildFresh I.MetaId TLState where
    nextFresh s = (freshMeta s, s { freshMeta = freshMeta s + 1 })

instance RM.HasGoal (ReaderT (I.ENamedCxt) TLM) where
    addGoal i g = modify $ \s -> s { subGoals = Map.insert i g (subGoals s) }
    removeGoal i = modify $ \s -> s { subGoals = Map.delete i (subGoals s) }
    mapGoal f = modify $ \s -> s { subGoals = Map.map f (subGoals s) }

instance RM.MonadRM (ReaderT (I.ENamedCxt) TLM)

runTLM :: TLM a -> IO (Either TopLevelErr a)
runTLM m = (Right <$> runTLM' m) `E.catch` (return . Left)

runTLM' :: TLM a -> IO a
runTLM' = flip evalUndoT initialTLState . unTLM

initialTLState :: TLState
initialTLState = TLState { global = E.emptyEnv, 
                           freshMeta = 0,
                           goal = Nothing,
                           subGoals = Map.empty,
                           currentSubGoal = Nothing  }


-- Lifted operations from TCM and RM

infer :: Expr -> TLM (I.Term, I.Type)
infer = flip runReaderT [] . T.infer

check :: Expr -> I.Term -> TLM I.Term
check e = flip runReaderT []  . T.check e

isSort :: I.Term -> TLM I.Sort
isSort = flip runReaderT [] . T.isSort

refine :: I.ENamedCxt -> Expr -> I.Term -> TLM I.ETerm
refine xs e t = flip runReaderT xs $ R.refine e t

refineSub :: I.ENamedCxt -> Expr -> I.ETerm -> TLM I.ETerm
refineSub xs e t = flip runReaderT xs $ fmap fst $ R.check e t

scope :: Expr -> TLM Expr
scope = flip runReaderT [] . S.scope 

scopeSub :: [Name] -> Expr -> TLM Expr
scopeSub xs = flip runReaderT xs . S.scope


-- Operations on the monad

runParserTLM :: FilePath -> GenParser tok () a -> [tok] -> TLM a
runParserTLM f p s = liftIO $ case runParser p () f s of
                                Left e -> throwIO $ MyParsingError e
                                Right t -> return t

addGlobal :: Name -> I.Type -> I.Term -> TLM ()
addGlobal x t u = do g <- fmap global get
                     when (E.bindedEnv x g) (throwIO $ AlreadyDefined x)
                     modify $ \s -> s { global = (E.extendEnv x (GE.Def t u) g) }

addAxiom :: Name -> I.Type -> TLM ()
addAxiom x t = do g <- fmap global get
                  when (E.bindedEnv x g) (throwIO $ AlreadyDefined x)
                  modify $ \s -> s { global = (E.extendEnv x (GE.Axiom t) g) }

normalForm :: I.Term -> TLM I.Term
normalForm = flip runReaderT [] . W.normalForm


showGlobal :: TLM ()
showGlobal = do g <- fmap global get
                liftIO $ putStr $ showEnv $ reverse $ E.listEnv g
    where showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
          showG (x, GE.Def t u) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
          showG (x, GE.Axiom t) = "axiom " ++ x ++ " : " ++ show t


showProof :: TLM ()
showProof = do g <- fmap goal get
               case g of
                 Just (x, t, e) -> liftIO $ putStrLn $ concat ["goal ", x, " : ", show t, " := ", show e]
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
         check (I.reify e) t -- check shouldn't fail
         addGlobal x t (I.downcast e)
         clearGoals

execCommand :: String -> TLM ()
execCommand xs = do csg <- fmap currentSubGoal get
                    case csg of
                      Nothing -> do c <- runParserTLM "<interactive>" parseTopLevelCommand xs
                                    processCommand c
                      Just (n, RM.Goal cxt t) -> do e <- runParserTLM "<interactive>" parseExprMeta xs
                                                    e1 <- scopeSub (map I.bind cxt) e
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
    where h :: E.SomeException -> TLM I.MetaId
          h = const $ throwIO UnknownGoal

setSubGoal :: I.MetaId -> TLM ()
setSubGoal n = do sg <- fmap subGoals get
                  case Map.lookup n sg of
                    Just goal -> modify $ \s -> s { currentSubGoal = Just (n,goal) }
                    Nothing -> throwIO $ UnknownGoal

setSomeSubGoal :: TLM ()
setSomeSubGoal = do sg <- fmap subGoals get
                    when (not (Map.null sg)) $ setSubGoal (fst (Map.findMin sg))
                      

processCommand :: Command -> TLM ()
processCommand (Definition x t u) = processDef x t u
processCommand (Axiom x t) = processAxiom x t
processCommand (Load xs) = processLoad xs
processCommand (Refine x t e) = do clearGoals
                                   t1 <- scope t
                                   (t', r) <- infer t1
                                   isSort r
                                   e1 <- scope e
                                   e' <- refine [] e1 t'
                                   modify $ \s -> s { goal = Just (x, t', e') }
                                   setSomeSubGoal

processLoad :: FilePath -> TLM ()
processLoad xs = do h <- liftIO $ openFile xs ReadMode
                    ss <- liftIO $ hGetContents h
                    cs <- runParserTLM xs parseFile ss
                    liftIO $ hClose h
                    forM_ cs processCommand

processAxiom :: Name -> Expr -> TLM ()
processAxiom x t = do t1 <- scope t
                      (t',r) <- infer t1
                      isSort r
                      addAxiom x t'

processDef :: Name -> Maybe Expr -> Expr -> TLM ()
processDef x (Just t) u = do t1 <- scope t
                             (t', r) <- infer t1
                             isSort r
                             u1 <- scope u
                             u' <- check u1 t'
                             addGlobal x t' u'
processDef x Nothing u = do u1 <- scope u
                            (u', r) <- infer u1
                            addGlobal x r u'

