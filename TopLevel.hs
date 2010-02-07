{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving,
  PackageImports, TypeSynonymInstances, MultiParamTypeClasses,
  FlexibleInstances, DeriveDataTypeable  #-}

module TopLevel where

import Prelude hiding (catch)
import Data.Char
import Data.List
import Data.Typeable

import Control.Applicative

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.IO

import Position
import Abstract
import MonadUndo
import TCM
import qualified Internal as I
import Parser
import qualified Typing as T
import qualified Environment as E
import Conversion
import Utils.Fresh

import qualified Refiner.Refiner as R
import qualified Refiner.RM as RM
import qualified Refiner.Environment as RE
import qualified Refiner.Internal as RI

addGlobal :: Name -> I.Type -> I.Term -> TLM ()
addGlobal x t u = do g <- get
                     let g' = global g
                     when (E.bindedEnv x g') (throwIO $ AlreadyDefined x)
                     put $ g { global = (E.extendEnv x (E.Def t u) g') }

addAxiom :: Name -> I.Type -> TLM ()
addAxiom x t = do g <- get
                  let g' = global g
                  when (E.bindedEnv x g') (throwIO $ AlreadyDefined x)
                  put $ g { global = (E.extendEnv x (E.Axiom t) g') }

data TCErr = TypeError TypeError
           | RefinerError RM.RefinerError
           | MyIOException E.IOException
           | ParsingError ParseError
           | AlreadyDefined String
           | InternalError String
           deriving(Typeable,Show)

instance Error TCErr where
    strMsg = InternalError

instance E.Exception TCErr


-- | Interaction monad.

data TLState = TLState { global :: E.GlobalEnv,
                         global2 :: RE.GlobalEnv,
                         freshMeta :: RI.MetaId,
                         goal :: Maybe RM.Goal,
                         subgoals :: [(RI.MetaId, RM.Goal)]
                       }

newtype TLM a = TLM { unTLM :: UndoT TLState IO a }
                deriving (Monad, 
                          Functor,
                          MonadUndo TLState,
                          MonadState TLState
                          )

instance MonadIO TLM where
  liftIO m = TLM $ liftIO $ m `E.catch` catchP `E.catch` catchIO `E.catch` catchT `E.catch` catchR
             where catchP :: ParseError -> IO a
                   catchP = E.throwIO . ParsingError
                   catchIO :: E.IOException -> IO a
                   catchIO = E.throwIO . MyIOException
                   catchT :: TypeError -> IO a
                   catchT = E.throwIO . TypeError
                   catchR :: RM.RefinerError -> IO a
                   catchR = E.throwIO . RefinerError


-- instance MonadError TypeError TLM where
--   throwError = liftIO . E.throwIO
--   catchError m h = TLM $ UndoT $ StateT $ \s -> ReaderT $ \r -> 
--     (runReaderT (runUndoT (unTLM m) (current s)) r)
--     `E.catch` \err -> runReaderT (runUndoT (unTLM (h err)) (current s)) r


-- liftTCMM :: TCM a -> TLM a
-- liftTCMM m = TLM $ StateT $ \(TLState s) -> (fmap (\(x,y) -> (x, TLState $ current y))) (runReaderT (runUndoT (unTCM m) s) initialTCEnv)

-- instance MonadTCM (ReaderT TCEnv TLM) where
--     liftTCM x = ReaderT $ \r -> TLM $ UndoT $ StateT $ \u -> u { global = (runTCM2 r (global (current u)) x) }

instance MonadTCM (ReaderT TCEnv TLM)

instance E.MonadGE (ReaderT TCEnv TLM) where
    lookupGE = f
               where f x = do g <- get
                              let g' = global g
                              case E.lookupEnv x g' of
                                Just t -> return t
                                Nothing -> throwIO $ IdentifierNotFound x

instance RE.MonadGE (ReaderT [RI.Term] TLM) where
    lookupGE = f
               where f x = do g <- get
                              let g' = global2 g
                              case RE.lookupEnv x g' of
                                Just t -> return t
                                Nothing -> throwIO $ IdentifierNotFound x

instance HasFresh RI.MetaId TLState where
    nextFresh s = (freshMeta s, s { freshMeta = freshMeta s + 1 })

instance RM.HasGoal (ReaderT [RI.Term] TLM) where
    getGoal = do s <- get
                 return $ subgoals s
    putGoal g = do s <- get
                   put $ s { subgoals = g }

instance RM.MonadRM TLState (ReaderT [RI.Term] TLM)

runTLM :: TLM a -> IO (Either TCErr a)
runTLM m = (Right <$> runTLM' m) `E.catch` (return . Left)

runTLM' :: TLM a -> IO a
runTLM' = -- flip runReaderT [] .
          flip evalUndoT initialTLState .
          unTLM

initialTLState = TLState { global = E.emptyEnv, 
                           global2 = RE.emptyEnv,
                           freshMeta = 0,
                           goal = Nothing,
                           subgoals = []
                         }


infer :: Expr -> TLM I.Term
infer = flip runReaderT [] . T.infer

check :: Expr -> I.Term -> TLM ()
check e t = flip runReaderT [] $ T.check e t

isSort :: I.Term -> TLM ()
isSort = flip runReaderT [] . T.isSort

type IM = InputT TLM

deriving instance MonadException TLM

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline = getInputLine

runIM :: IM a -> TLM a
runIM = runInputT settings
        where settings :: Settings TLM
              settings = defSettings { complete = completion }
              defSettings :: Settings TLM
              defSettings = defaultSettings

catchIM :: TLM () -> IM ()
catchIM m = lift m `catch` f
            where f :: TCErr -> IM ()
                  f e = outputStrLn (show e)

data TLCommand = LoadFile String
               | Check String
               | Eval String
               | Print
               | Undo
               | Redo
               | Quit
               | Help
               | NoOp
               | NoCommand String
               deriving(Show)

data InteractiveCommand = Cmd [String] String (String -> TLCommand) String

cmdName (Cmd xs _ _ _) = xs

commands :: [InteractiveCommand]
commands
    =  [ Cmd [":type"]        "<expr>"  Check          "print type of expression",
         Cmd [":load"]        "<file>"  LoadFile       "load program from file",
         Cmd [":eval"]        "<expr>"  Eval           "evaluates an expression to normal form",
         Cmd [":print"]       ""        (const Print)  "print all global definitions",
         Cmd [":undo"]        ""        (const Undo)   "undo last action",
         Cmd [":redo"]        ""        (const Redo)   "redo last action",
         Cmd [":quit"]        ""        (const Quit)   "exit interpreter",
         Cmd [":help",":?"]   ""        (const Help)   "display this list of commands" ]


interpretCommand :: String -> IM TLCommand
interpretCommand x
    =  if isPrefixOf ":" x then
         do  let  (cmd,t')  =  break isSpace x
                  t         =  dropWhile isSpace t'
             --  find matching commands
             let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
             case matching of
               [] -> do outputStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                        return NoOp
               [Cmd _ _ f _] ->  return (f t)
               x -> do outputStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                       return NoOp
       else
         return $ NoCommand x


interactiveLoop :: IM ()
interactiveLoop = do xs <- readline "> "
                     case xs of
                       Nothing -> return ()
                       Just xs -> do c <- interpretCommand xs
                                     processTLCommand c
                                     case c of
                                       Quit -> return ()
                                       _ -> interactiveLoop

processTLCommand :: TLCommand -> IM ()
processTLCommand (Check s) = catchIM $ do e <- liftIO $ runParserIO "<interactive>" (parseEOF (parseExpr False)) s
                                          (infer e) >>= liftIO . print
-- processTLCommand (Eval s) = catchIM $ do e <- liftIO $ runParserIO "<interactive>" (parseEOF parseExpr) s
--                                          _ <- infer e
--                                          v <- norm (I.interp e)
--                                          lift $ print (valterm v)
processTLCommand Help = outputStrLn "help coming"
processTLCommand Print = do g <- lift get
                            let g' = global g
                            outputStr $ showEnv $ reverse $ E.listEnv g'
                where showEnv :: [(Name, E.Global)] -> String
                      showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
                      showG (x, E.Def t u) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
                      showG (x, E.Axiom t) = "axiom " ++ x ++ " : " ++ show t
processTLCommand (LoadFile xs) = catchIM $ oneStep $ processLoad (takeWhile (not . isSpace) xs)
processTLCommand Undo = do b <- lift undo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand Redo = do b <- lift redo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand NoOp = return ()
processTLCommand Quit = return ()
processTLCommand (NoCommand xs) = catchIM $ do c <- liftIO $ runParserIO "<interactive>" (parseEOF parseCommand) xs
                                               processCommand c


processCommand :: Command -> TLM ()
processCommand (Definition x t u) = processDef x t u
processCommand (Axiom x t) = processAxiom x t
processCommand (Load xs) = processLoad xs

processLoad :: FilePath -> TLM ()
processLoad xs = do h <- liftIO $ openFile xs ReadMode
                    ss <- liftIO $ hGetContents h
                    cs <- liftIO $ runParserIO xs (parseEOF parseFile) ss
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


--------- Completion
completion :: CompletionFunc TLM
completion line@(left,_) = case firstWord of
    ':':cmd     | null rest     -> completeCmd line
                | otherwise     -> completeFilename line
    xs          | null rest     -> completeDecl line
                | otherwise     -> completeGlobal line
  where
    (firstWord,rest) = break isSpace $ dropWhile isSpace $ reverse left

completeCmd :: (String, String) -> TLM (String, [Completion])
completeCmd = wrapCompleter " " $ \w -> do
                return (filter (w `isPrefixOf`) (concat (map cmdName commands)))

completeDecl :: (String, String) -> TLM (String, [Completion])
completeDecl = wrapCompleter " " $ \w -> do
                 return (filter (w `isPrefixOf`) ["let", "axiom"])

completeGlobal :: (String, String) -> TLM (String, [Completion])
completeGlobal = wrapCompleter " " $ \w -> do g <- get
                                              let g' = global g 
                                              return (filter (w `isPrefixOf`) (map fst (E.listEnv g')))


wrapCompleter :: String -> (String -> TLM [String]) -> CompletionFunc TLM
wrapCompleter breakChars fun = completeWord Nothing breakChars
    $ fmap (map simpleCompletion) . fmap sort . fun
