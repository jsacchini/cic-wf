{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving,
  PackageImports, TypeSynonymInstances, MultiParamTypeClasses,
  FlexibleInstances, DeriveDataTypeable  #-}

module TopLevel.TopLevel where

import Prelude hiding (catch)
import Data.Char
import Data.List
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
import Parser
import qualified Kernel.TypeChecking as T
import qualified Environment as E
import Utils.Fresh
import Utils.Misc

import qualified Refiner.RM as RM

import TopLevel.Monad

type IM = InputT TLM

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
                  f = outputStrLn . show



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
               -- Goal commands
               | SetGoal String
               | Qed
               | ShowContext
               | ShowGoal
               | ListGoals
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
         Cmd [":help",":?"]   ""        (const Help)   "display this list of commands",
         Cmd [":context"]     ""        (const ShowContext) "show current goal context",
         Cmd [":qed"]         ""        (const Qed)    "finishes proof",
         Cmd [":set"]         ""        SetGoal        "sets a new subgoal",
         Cmd [":show"]        ""        (const ShowGoal) "show goal",
         Cmd [":goals"]       ""        (const ListGoals) "list all goals"
       ]


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


readPrompt :: IM (Maybe String)
readPrompt = do pr <- showPrompt
                readline pr
    where showPrompt = lift $ do g <- get
                                 case currentSubGoal g of
                                   Nothing -> return "> "
                                   Just (n,_) -> return $ show n ++ " > "

interactiveLoop :: IM ()
interactiveLoop = do xs <- readPrompt
                     case xs of
                       Nothing -> return ()
                       Just xs -> do c <- interpretCommand xs
                                     processTLCommand c
                                     case c of
                                       Quit -> return ()
                                       _ -> interactiveLoop

processTLCommand :: TLCommand -> IM ()
processTLCommand (Check s) = catchIM $ do e <- runParserTLM "<interactive>" (parseEOF (parseExpr pVar)) s
                                          infer e >>= liftIO . print
processTLCommand (Eval s) = catchIM $ do e <- runParserTLM "<interactive>" (parseEOF (parseExpr pVar)) s
                                         _ <- infer e
                                         v <- normalForm e
                                         liftIO $ print v
processTLCommand Help = outputStrLn "help coming"
processTLCommand Print = lift showGlobal >>= outputStr
processTLCommand (LoadFile xs) = catchIM $ oneStep $ processLoad (takeWhile (not . isSpace) xs)
processTLCommand Undo = do b <- lift undo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand Redo = do b <- lift redo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand NoOp = return ()
processTLCommand Quit = return ()
processTLCommand (NoCommand xs) = catchIM $ execCommand xs
processTLCommand (SetGoal xs) = let g = read xs::I.MetaId in
                                catchIM $ setSubGoal g
processTLCommand ShowGoal = lift showGoal >>= outputStrLn
processTLCommand ShowContext = lift showContext >>= outputStrLn
processTLCommand ListGoals = lift listGoals >>= outputStrLn
processTLCommand Qed = catchIM qed

--------- Completion
completion :: CompletionFunc TLM
completion line@(left,_) = case firstWord of
    ':':_       | null rest     -> completeCmd line
                | otherwise     -> completeFilename line
    _           | null rest     -> completeDecl line
                | otherwise     -> completeGlobal line
  where
    (firstWord,rest) = break isSpace $ dropWhile isSpace $ reverse left

completeCmd :: (String, String) -> TLM (String, [Completion])
completeCmd = wrapCompleter " " $ \w ->
                return (filter (w `isPrefixOf`) (concatMap cmdName commands))

completeDecl :: (String, String) -> TLM (String, [Completion])
completeDecl = wrapCompleter " " $ \w ->
                 return (filter (w `isPrefixOf`) ["let", "axiom"])

completeGlobal :: (String, String) -> TLM (String, [Completion])
completeGlobal = wrapCompleter " " $ \w -> do g <- get
                                              let g' = global g 
                                              return (filter (w `isPrefixOf`) (map fst (E.listEnv g')))


wrapCompleter :: String -> (String -> TLM [String]) -> CompletionFunc TLM
wrapCompleter breakChars fun = completeWord Nothing breakChars
    $ fmap (map simpleCompletion . sort) . fun
