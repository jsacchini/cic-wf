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
import Utils.MonadUndo
import Kernel.TCM
import qualified Kernel.Whnf as W
import qualified Syntax.Internal as I
import Syntax.ETag
import qualified Kernel.TypeChecking as T
import qualified Environment as E
import Utils.Fresh
import Utils.Misc
import Parser

import qualified Refiner.RM as RM
import qualified Refiner.Refiner as R
import qualified Refiner.Unify as RU


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
           | UnknownGoal I.MetaId
           deriving(Typeable,Show)

instance Error TCErr where
    strMsg = InternalError

instance E.Exception TCErr


-- | Interaction monad.

data TLState = TLState { global :: E.GlobalEnv NM,
                         freshMeta :: I.MetaId,
                         goal :: Maybe (Name, I.Type NM, I.Term EVAR),
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

instance E.MonadGE (ReaderT r TLM) where
    lookupGE x = do g <- get
                    return $ E.lookupEnv x (global g)

instance BuildFresh I.MetaId TLState where
    nextFresh s = (freshMeta s, s { freshMeta = freshMeta s + 1 })

instance RM.HasGoal (ReaderT (I.NamedCxt EVAR) TLM) where
    addGoal i g = do s <- get
                     put $ s { subGoals = Map.insert i g (subGoals s) }
    removeGoal i = do s <- get
                      put $ s { subGoals = Map.delete i (subGoals s) }

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
                           subGoals = Map.empty,
                           currentSubGoal = Nothing
                         }


infer :: Expr -> TLM (I.Term NM)
infer = flip runReaderT [] . T.infer

check :: Expr -> I.Term NM -> TLM ()
check e = flip runReaderT [] . T.check e

isSort :: I.Term NM -> TLM ()
isSort = flip runReaderT [] . T.isSort

refine :: I.NamedCxt EVAR -> Expr -> I.Term NM -> TLM (I.Term EVAR)
refine xs e t = flip runReaderT xs $ R.refine e t

refineSub :: I.NamedCxt EVAR -> Expr -> I.Term EVAR -> TLM (I.Term EVAR)
refineSub xs e t = flip runReaderT xs $ fmap fst $ R.check e t

normalForm :: Expr -> TLM (I.Term NM)
normalForm = flip runReaderT [] . W.normalForm . I.interp


runParserTLM :: FilePath -> GenParser tok () a -> [tok] -> TLM a
runParserTLM f p s = liftIO $ case runParser p () f s of
                                Left e -> throwIO $ MyParsingError e
                                Right t -> return t


showGlobal :: TLM String
showGlobal = do g <- get
                return $ showEnv $ reverse $ E.listEnv (global g)
    where showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
          showG (x, I.Def t u) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
          showG (x, I.Axiom t) = "axiom " ++ x ++ " : " ++ show t


showGoal :: TLM String
showGoal = do s <- get
              case goal s of
                Just (x, t, e) -> return $ "goal " ++ x ++ " : " ++ show t ++ " := " ++ show e
                Nothing -> return $ "No goal"

showContext :: TLM String
showContext = do s <- get
                 case currentSubGoal s of
                   Just (i, g) -> return $ show g
                   Nothing -> return $ "No current goal"


setSubGoal :: I.MetaId -> TLM ()
setSubGoal n = do g <- get
                  let sg = subGoals g in
                   case Map.lookup n sg of
                     Just goal -> put $ g { currentSubGoal = Just (n,goal),
                                            subGoals = Map.delete n sg }
                     Nothing -> throwIO $ UnknownGoal n

listGoals :: TLM String
listGoals = do g <- get
               return $ Map.foldWithKey (\n sg r -> show n ++ " : " ++ RM.showGoalType sg ++ "\n" ++ r) "" (subGoals g)

-- refineCurrent :: Expr -> TLM ()

clearGoals :: TLM ()
clearGoals = do s <- get
                put $ s { goal = Nothing,
                          subGoals = Map.empty,
                          currentSubGoal = Nothing,
                          freshMeta = 0
                        }


qed :: TLM ()
qed = do sg <- fmap subGoals get
         when (not (Map.null sg)) $ liftIO (print "Not finished") >> return ()
         cg <- fmap currentSubGoal get
         when (isJust cg) $ liftIO (print "Not finished") >> return ()
         Just (x, t, e) <- fmap goal get
         check (I.reify e) (I.cast t) -- cast shouldn't fail
         addGlobal x (I.cast t) (I.cast e)

execCommand :: String -> TLM ()
execCommand xs = do csg <- fmap currentSubGoal get
                    case csg of
                      Nothing -> do c <- runParserTLM "<interactive>" (parseEOF (parseCommand pVar)) xs
                                    processCommand c
                      Just (n, RM.Goal cxt t) -> do e <- runParserTLM "<interactive>" (parseEOF (parseExpr pIdentMeta)) xs
                                                    e' <- refineSub cxt e t
                                                    cg <- fmap goal get
                                                    modify $ \s -> s { goal = fmap (\(x,t,e) -> (x,t,RU.apply [(n,e')] e)) cg,
                                                                       currentSubGoal = Nothing
                                                                     }
                                                    setSomeSubGoal
                                 
setSomeSubGoal :: TLM ()
setSomeSubGoal = do sg <- fmap subGoals get
                    when (not (Map.null sg)) $ setSubGoal (fst (Map.findMin sg))
                      

processCommand :: Command -> TLM ()
processCommand (Definition x t u) = processDef x t u
processCommand (Axiom x t) = processAxiom x t
processCommand (Load xs) = processLoad xs
processCommand (Refine x t e) = do clearGoals
                                   t' <- infer t
                                   e' <- refine [] e t'
                                   modify $ \s -> s { goal = Just (x, t', e') }
                                   setSomeSubGoal

processLoad :: FilePath -> TLM ()
processLoad xs = do h <- liftIO $ openFile xs ReadMode
                    ss <- liftIO $ hGetContents h
                    cs <- runParserTLM xs (parseEOF parseFile) ss
                    liftIO $ hClose h
                    forM_ cs processCommand

processAxiom :: Name -> Expr -> TLM ()
processAxiom x t = do r <- infer t
                      isSort r
                      addAxiom x (I.interp t)

processDef :: Name -> Maybe Expr -> Expr -> TLM ()
processDef x (Just t) u = do check u (I.interp t)
                             addGlobal x (I.interp t) (I.interp u)
processDef x Nothing u = do t <- infer u
                            addGlobal x t (I.interp u)

