{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving,
  PackageImports, TypeSynonymInstances, MultiParamTypeClasses,
  FlexibleInstances, DeriveDataTypeable  #-}

module TopLevel.TopLevel where

import Prelude hiding (catch)
import Data.Char
import Data.List
import Data.Maybe
import Data.Typeable
import qualified Data.Map as Map

import Control.Applicative

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
--import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.IO

import Syntax.Abstract
import Utils.MonadUndo
import Kernel.TCM
import Kernel.Command
import qualified Syntax.Internal as I
import Syntax.ETag
import Syntax.Parser
import qualified Kernel.TypeChecking as T
import qualified Kernel.GlobalMonad as GM
import qualified Environment as E
import Utils.Fresh
import Utils.Misc

import qualified Refiner.RM as RM

import TopLevel.Monad

type IM = InputT TLM

-- | Line reader. The line reader history is not stored between
-- sessions.

runIM :: IM a -> TLM a
runIM = runInputT settings
        where settings :: Settings TLM
              settings = defSettings { complete = completion,
                                       historyFile = Just "/home/jorge/.cicminus-history" }
              defSettings :: Settings TLM
              defSettings = defaultSettings

handleIM :: TLM () -> IM ()
handleIM m = lift m `catch` f
             where f :: TopLevelErr -> IM ()
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
               | ShowCommand String
               | ListGoals
               | Reset
               deriving(Show)

data InteractiveCommand = Cmd [String] String ([String] -> Bool) (String -> TLCommand) String (CompletionFunc TLM)

cmdName (Cmd xs _ _ _ _ _) = xs

commands :: [InteractiveCommand]
commands = syntax
    where syntax =
              [ Cmd [":type"]        "<expr>"  none Check   "print type of expression"               completeGlobal,
                Cmd [":load"]        "<file>"  arg  LoadFile         "load program from file"                 completeFilename,
                Cmd [":eval"]        "<expr>"  none Eval    "evaluates an expression to normal form" completeGlobal,
                Cmd [":print"]       ""        arg0 (const Print)    "print all global definitions"           noCompletion,
                Cmd [":undo"]        ""        arg0 (const Undo)     "undo last action"                       noCompletion,
                Cmd [":redo"]        ""        arg0 (const Redo)     "redo last action"                       noCompletion,
                Cmd [":quit"]        ""        arg0 (const Quit)     "exit interpreter"                       noCompletion,
                Cmd [":help",":?"]   ""        arg0 (const Help)     "display this list of commands"          noCompletion,
                Cmd [":qed"]         ""        arg0 (const Qed)      "finishes proof"                         noCompletion,
                Cmd [":set"]         "<goal>"  arg1 SetGoal "sets a new subgoal"                     (completeFirstArg completeGoal),
                Cmd [":show"]        (concat $ intersperse " | " showSub)
                                               arg1 ShowCommand "show stuff"                        showCompletion,
                Cmd [":reset"]       ""        arg0 (const Reset)    "reset current goal"                     noCompletion
              ]
          none = const True
          arg = (>0) . length
          argN n = (==n) . length
          arg1 = argN 1
          arg0 = argN 0
          showSub = map fst showSubcommands
          showCompletion = completeFirstArg $ completeWords showSub -- need a better completion

findMatching :: String -> [InteractiveCommand]
findMatching cmd = filter (\ (Cmd cs _ _ _ _ _) -> any (isPrefixOf cmd) cs) commands

showSubcommands = [("proof", showProof),
                   ("goals", showGoals),
                   ("context", showContext)]

showHelp xs = "syntax: " ++ (concat $ map printHelp $ findMatching xs)
              where printHelp (Cmd cs s _ _ _ _) = unwords [head cs, s, "\n"]

interpretCommand :: String -> IM TLCommand
interpretCommand x
    =  if isPrefixOf ":" x then
         do  let  (cmd,t')  =  break isSpace x
                  t         =  dropWhile isSpace t'
             --  find matching commands
             let  matching  =  findMatching cmd
             case matching of
               [] -> do outputStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                        return NoOp
               [Cmd ns as argCheck f _ _] -> if argCheck $ words t
                                             then return (f t)
                                             else do outputStr $ showHelp $ head ns
                                                     return NoOp
               x -> do outputStrLn ("Ambiguous command, could be " ++
                                    concat (intersperse ", " (map (head . cmdName) matching)) ++ ".")
                       return NoOp
       else
         return $ NoCommand x


readPrompt :: IM (Maybe String)
readPrompt = do pr <- lift get >>= showPrompt
                getInputLine pr
    where showPrompt g = let pm = if isJust (goal g) then "pr " else ""
                             gn = case currentSubGoal g of
                                    Nothing -> ""
                                    Just (n,_) -> "(" ++ show n ++ ") "
                         in return $ pm ++ gn ++ "> "

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
processTLCommand (Check s) = handleIM $ do e <- runParser "<interactive>" parseExpr s
                                           GM.scope e >>= GM.infer >>= liftIO . putStrLn . I.ppTerm [] . snd
processTLCommand (Eval s) = handleIM $ do e <- runParser "<interactive>" parseExpr s
                                          (e',_) <- GM.infer e
                                          v <- GM.normalForm e'
                                          liftIO $ putStrLn $ I.ppTerm [] v
processTLCommand Help = outputStrLn "help coming"
processTLCommand Print = handleIM showGlobal
processTLCommand (LoadFile fs) = handleIM $ oneStep $ processLoad (head $ words fs)
processTLCommand Undo = do b <- lift undo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand Redo = do b <- lift redo
                           if b then outputStrLn "si" else outputStrLn "no"
processTLCommand NoOp = return ()
processTLCommand Quit = return ()
processTLCommand (NoCommand xs) = handleIM $ oneStep $ execCommand xs
processTLCommand (SetGoal xs) = handleIM $ oneStep $ readAndSetSubGoal xs
processTLCommand (ShowCommand xs) = case filter (\(s, f) -> isPrefixOf arg s) showSubcommands of
                                      [(_,f)] -> handleIM f
                                      _ -> outputStr $ showHelp ":show"
                                    where [arg] = words xs
processTLCommand Qed = handleIM $ oneStep qed
processTLCommand Reset = handleIM $ oneStep clearGoals

--------- Completion
completion :: CompletionFunc TLM
completion line@(left,_) = case firstWord of
    ':':_       | null rest     -> completeCmd line
                | otherwise     -> case matching of
                                     [(Cmd _ _ _ _ _ f)] -> f line
                                     _ -> noCompletion line
    _           | null rest     -> completeDecl line
                | otherwise     -> completeGlobal line
  where
    (firstWord,rest) = break isSpace $ dropWhile isSpace $ reverse left
    matching = findMatching $ firstWord

-- applies the argument if it's trying to complete the second word
completeFirstArg :: CompletionFunc TLM -> CompletionFunc TLM
completeFirstArg f line@(left, right) = if not (null rest) && null allRest then f line else noCompletion line
    where (firstWord, rest) = break isSpace $ dropWhile isSpace $ reverse left
          (secondWord, allRest) = break isSpace $ dropWhile isSpace rest

completeCmd :: CompletionFunc TLM
completeCmd = completeWords (concat $ map cmdName commands)

completeDecl :: CompletionFunc TLM
completeDecl = completeWords ["let", "axiom"]

completeGlobal :: (String, String) -> TLM (String, [Completion])
completeGlobal = wrapCompleter " " $ \w -> do g <- get
                                              let g' = global g
                                              return (filter (w `isPrefixOf`) (map fst (E.listEnv g')))

completeGoal :: (String, String) -> TLM (String, [Completion])
completeGoal = wrapCompleter " " $ \w -> do sg <- fmap subGoals get
                                            return (filter (w `isPrefixOf`) (map show $ Map.keys sg))

completeWords :: [String] -> CompletionFunc TLM
completeWords xs = wrapCompleter " " $ \w -> return (filter (w `isPrefixOf`) xs)

wrapCompleter :: String -> (String -> TLM [String]) -> CompletionFunc TLM
wrapCompleter breakChars fun = completeWord Nothing breakChars
    $ fmap (map simpleCompletion . sort) . fun
