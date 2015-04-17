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

module Main where

import           System.Console.GetOpt
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO

import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.State

import           CICwf.Syntax.AbstractToConcrete
import qualified CICwf.Syntax.Concrete           as C
import           CICwf.Syntax.ParseMonad
import           CICwf.Syntax.Parser
import           CICwf.Syntax.Scope

import           CICwf.TypeChecking.Declaration
import           CICwf.TypeChecking.PrettyTCM
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors


data Options =
  Options { optVerbose :: Int -- Verbosity
          , optSolveConstraints :: Bool
          } deriving Show

defaultOptions :: Options
defaultOptions =
  Options { optVerbose = 1
          , optSolveConstraints = True }

options :: [OptDescr (Options -> Options)]
options =
  [ Option "v" ["verbose"]
    (ReqArg (\n opts -> opts { optVerbose = read n }) "integer")
    "set verbosity level"
  , Option "c" ["do-not-solve-constraints"]
    (NoArg (\opts -> opts { optSolveConstraints = False }))
    "whether to solve constraints"
  ]


main :: IO ()
-- main = runTop mainLoop
main = evalFile

evalFile :: IO ()
evalFile =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     case getOpt RequireOrder options args of
       (o,n,[])   -> do mapM_ (runFile opts) n
                        exitSuccess
                          where opts = foldl (flip id) defaultOptions o
       (_,_,errs) -> putStrLn $ "Command line error: " ++ concat errs
     -- mapM_ runFile args
    where
      runFile opts f =
        do h <- openFile f ReadMode
           ss <- hGetContents h
           case parse fileParser (Just $ snd $ splitFileName f) ss of
             ParseOk ts ->
               do  r <- runTCMIO (typeCheckFile opts ts
                                  `catch` printError)
                   case r of
                     Right _ -> exitSuccess
                     Left _  -> exitFailure
             ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
           hClose h
      printError :: (MonadTCM tcm) => TCErr -> tcm ()
      printError err = do
        prettyError err
        throwM err

      typeCheckFile :: Options -> [C.Declaration] -> TCM ()
      typeCheckFile opts ds =
        do setVerbosity (optVerbose opts)
           setSolveConstraints (optSolveConstraints opts)
           forM_ ds (scope >=> inferDecl)
