{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses,
    UndecidableInstances
  #-}

module TopLevel.TopLevel where

import Prelude hiding (catch)

import Control.Monad.State

import Data.Char
import Data.Functor
import Data.List

import qualified Text.PrettyPrint as PP

import Syntax.Common
import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope

import Kernel.TCM
import Kernel.PrettyTCM
import Kernel.TypeChecking

import TopLevel.Monad


-- | Top-level commands

data Command = ListGoals
             | SetGoal Int
             | LoadFile FilePath
             | Reset
             | Help
             | Show
             | Quit
             | NoOp
             | NoCommand String
             deriving(Show)


data CommandSpec = Spec [String] String ([String] -> Bool) (String -> Command) String --(CompletionFunc TLM)

commands :: [CommandSpec]
commands =
  [ Spec
    [":goals"]
    ""
    none
    (const ListGoals)
    "show the remaining goals"
  , Spec
    [":setgoal"]
    "number"
    arg1
    (SetGoal . read)
    "show the remaining goals"
  , Spec
    [":show"]
    ""
    none
    (const Show)
    "show current goal context"
  , Spec
    [":help", ":?"]
    ""
    none
    (const Help)
    "show help"
  , Spec
    [":quit"]
    ""
    none
    (const Quit)
    "quits"
  ]
  where
    none = const True
    args = (>0) . length
    argN n = (==n) . length
    arg1 = argN 1
    arg0 = argN 0


cmdName (Spec xs _ _ _ _) = xs

findMatching :: String -> [CommandSpec]
findMatching cmd = filter (\ (Spec cs _ _ _ _) -> any (isPrefixOf cmd) cs) commands

showHelp xs = "syntax: " ++ (concat $ map printHelp $ findMatching xs)
  where printHelp (Spec cs s _ _ _) = unwords [head cs, s, "\n"]

readCommand :: String -> TopM Command
readCommand x | isPrefixOf ":" x =
  do let (cmd,t') = break isSpace x
         t        = dropWhile isSpace t'
         --  find matching commands
     case findMatching cmd of
       [] -> do outputStrLn ("Unknown command `" ++ cmd ++ "'. Type :? for help.")
                return NoOp
       [Spec ns as argCheck f _] -> if argCheck $ words t
                                      then return (f t)
                                      else do outPutStr $ showHelp $ head ns
                                              return NoOp
       x -> do outputStrLn ("Ambiguous command, could be " ++
                            concat (intersperse ", " (map (head . cmdName) x)) ++ ".")
               return NoOp
              | otherwise = return $ NoCommand x

showPrompt :: TopM ()
showPrompt = liftTop $ showPrompTCM
  where
    showPrompTCM = do g <- getActiveGoal
                      liftIO $ putStr $ goalPrompt g
    goalPrompt (Just (x, _)) = "?" ++ show x ++ " > "
    goalPrompt Nothing  = "> "

ppGoal :: (MonadTCM tcm) => (MetaVar, Goal) -> tcm Doc
ppGoal (k, g) = text "Goal " <> prettyPrintTCM k $$ prettyPrintTCM g

evalCommand :: Command -> TopM ()
evalCommand Quit = return ()
evalCommand ListGoals = do
  liftTop $ do gs <- listGoals
               liftIO $ putStrLn $ "Number of goals: " ++ show (length gs)
               d <- vcat (map ppGoal gs)
               liftIO $ putStrLn (PP.render d)
  mainLoop
evalCommand (SetGoal k) = do
  liftTop $ do g <- getGoal (toEnum k)
               case g of
                 Just g -> case goalTerm g of
                             Nothing -> setActiveGoal (Just (toEnum k))
                             Just _  -> liftIO $ putStrLn "Goal does not exists"
                 Nothing -> liftIO $ putStrLn "Goal does not exists"
  mainLoop
evalCommand Show = do
  liftTop $ do ag <- getActiveGoal
               case ag of
                 Nothing -> do sig <- map (fmap eraseSize) <$> getSignature
                               let sig' = filter (not . isConstr . namedValue) sig
                               printTCMLn $ vcat (map ( (<> dot) . prettyPrintTCM) sig')
                 Just (k, g) -> do d <- ppGoal (k, g)
                                   liftIO $ putStrLn (PP.render d)
  mainLoop
evalCommand (NoCommand x) = do
  liftTop $ do
    g <- getActiveGoal
    case g of
      Nothing -> evalDeclaration x
      Just _  -> evalExpression x
  mainLoop
evalCommand NoOp = mainLoop

mainLoop :: TopM ()
mainLoop = do
  showPrompt
  minput <- getInputLine ""
  case minput of
    Nothing -> mainLoop
    Just x -> readCommand x >>= evalCommand

evalDeclaration :: (MonadTCM tcm) => String -> tcm ()
evalDeclaration ss =
  case parse fileParser ss of
    ParseOk ts -> typeCheckFile ts
      -- do r <- runTCM $ typeCheckFile ts
      --    case r of
      --      Left err -> putStrLn $ "Error!!!! " ++ show err
      --      Right _ -> return ()
    ParseFail err -> liftIO $ putStrLn $ "Error (Main.hs): " ++ show err

evalExpression :: (MonadTCM tcm) => String -> tcm ()
evalExpression ss =
  case parse exprParser ss of
    ParseOk ts -> do
      (Just (k, g)) <- getActiveGoal
      e <- withEnv (goalEnv g) $ scope ts
      t <- withEnv (goalEnv g) $ check e (goalType g)
      giveTerm k t
      setActiveGoal Nothing
    ParseFail err -> liftIO $ putStrLn $ "Error (Main.hs): " ++ show err

typeCheckDecl :: (MonadTCM tcm) => A.Declaration -> tcm ()
typeCheckDecl d = do d' <- scope d
                     traceTCM 30 $ hsep [ text "  INFER GLOBAL DECL: "
                                        , prettyPrintTCM d' ]
                     gs <- inferDecl d'
                     forM_ gs addGlobal

typeCheckFile :: (MonadTCM tcm) => [A.Declaration] -> tcm ()
typeCheckFile ds =
  do forM_ ds typeCheckDecl
