{-# LANGUAGE PackageImports, TypeSynonymInstances, MultiParamTypeClasses #-}

module TopLevel where

import Data.Char
import Data.List

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.IO

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import qualified Environment as E
import Conversion

-- | Interaction monad.

type IM = TCM (InputT IO)

instance MonadError TCErr IM where
  throwError = liftIO . throwIO
  catchError m h = mapTCMT liftIO $ runIM m `catchError` (runIM . h)

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline = lift . getInputLine

runIM :: IM a -> Result a
runIM = mapTCMT (runInputT defaultSettings)

catchIM :: Result () -> IM ()
catchIM = liftTCM . (`catchError` \e -> liftIO $ print e)

data TLCommand = LoadFile String
               | Check String
               | Eval String
               | Print
               | Quit
               | Help
               | NoOp
               | NoCommand String
               deriving(Show)

data InteractiveCommand = Cmd [String] String (String -> TLCommand) String

commands :: [InteractiveCommand]
commands
    =  [ Cmd [":type"]        "<expr>"  Check          "print type of expression",
         Cmd [":load"]        "<file>"  LoadFile       "load program from file",
         Cmd [":eval"]        "<expr>"  Eval           "evaluates an expression to normal form",
         Cmd [":print"]       ""        (const Print)  "print all global definitions",
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
               [] -> do lift $ outputStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                        return NoOp
               [Cmd _ _ f _] ->  return (f t)
               x -> do lift $ outputStrLn ("Ambiguous command, could be " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
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

parseExprEOF = do e <- parseExpr
                  eof
                  return e

processTLCommand :: TLCommand -> IM ()
processTLCommand (Check s) = catchIM $ do e <- liftIO $ runParserIO "<interactive>" (parseEOF parseExpr) s
                                          infer e >>= lift . print
-- processTLCommand (Eval s) = catchIM $ do e <- liftIO $ runParserIO "<interactive>" (parseEOF parseExpr) s
--                                          _ <- infer e
--                                          v <- norm (I.interp e)
--                                          lift $ print (valterm v)
processTLCommand Help = lift $ outputStrLn "help coming"
processTLCommand Print = do g <- get
                            lift $ outputStr $ showEnv $ reverse $ E.listEnv g
                where showEnv :: [(Name, E.Global)] -> String
                      showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
                      showG (x, E.Def t u) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
                      showG (x, E.Axiom t) = "axiom " ++ x ++ " : " ++ show t
processTLCommand (LoadFile xs) = catchIM $ processLoad (takeWhile (not . isSpace) xs)
processTLCommand NoOp = return ()
processTLCommand Quit = return ()
processTLCommand (NoCommand xs) = catchIM $ do c <- liftIO $ runParserIO "<interactive>" (parseEOF parseCommand) xs
                                               processCommand c


processCommand :: Command -> Result ()
processCommand (Definition x t u) = processDef x t u
processCommand (Axiom x t) = processAxiom x t
processCommand (Load xs) = processLoad xs

processLoad :: FilePath -> Result ()
processLoad xs = do h <- liftIO $ openFile xs ReadMode
                    ss <- liftIO $ hGetContents h
                    cs <- liftIO $ runParserIO xs (parseEOF parseFile) ss
                    liftIO $ hClose h
                    forM_ cs (liftTCM . processCommand)

processAxiom :: Name -> Expr -> Result ()
processAxiom x t = do r <- infer t
                      isSort r
                      addAxiom x (I.interp t)

processDef :: Name -> Maybe Expr -> Expr -> Result ()
processDef x (Just t) u = do check u (I.interp t)
                             addGlobal x (I.interp t) (I.interp u)
processDef x Nothing u = do t <- infer u
                            addGlobal x t (I.interp u)


