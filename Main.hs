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

module Main where

import Prelude hiding (catch)

import System.Console.GetOpt
import System.Environment

import System.IO

import Control.Monad.Trans
import Control.Monad.State
import Data.Functor
import Data.List
import Data.Maybe

import qualified Text.PrettyPrint as PP

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope
import Syntax.Internal

import qualified Utils.Pretty as MP

import qualified TypeChecking.Constraints as CS
import TypeChecking.TCM
import TypeChecking.PrettyTCM
import TypeChecking.TypeChecking
import Syntax.InternaltoAbstract

import TopLevel.Monad
import TopLevel.TopLevel


data Options =
  Options { optVerbose :: Verbosity
          } deriving Show

defaultOptions :: Options
defaultOptions =
  Options { optVerbose = 1 }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['v'] ["verbose"]
    (ReqArg (\n opts -> opts { optVerbose = read n }) "integer")
    "set verbosity level"
  ]

main :: IO ()
-- main = runTop mainLoop
main = evalFile

evalFile =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     case getOpt RequireOrder options args of
       (o,n,[])   -> mapM_ (runFile opts) n
                     where opts = foldl (flip id) defaultOptions o
       (_,_,errs) -> putStrLn $ "Command line error: " ++ concat errs
     -- mapM_ runFile args
    where runFile opts f =
            do h <- openFile f ReadMode
               ss <- hGetContents h
               case parse fileParser ss of
                 ParseOk ts ->
                   do -- putStrLn "OK"
                      -- putStrLn $ show ts
                      -- putStrLn "===================\n=================\n\n"
                      putStrLn $ PP.render $ MP.prettyPrint ts
                      r <- runTCM $ typeCheckFile (optVerbose opts) ts
                      case r of
                        Left err -> putStrLn $ "Error!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d =
            do
              resetConstraints
              d' <- scope d
              traceTCM 30 $ hsep [ text "  INFER GLOBAL DECL: "
                                 , prettyPrintTCM d' ]
              gs <- inferDecl d'
              forM_ gs addGlobal
              -- traceTCM 30 $ (text "  INFERRED GLOBAL DECL: (SHOW)"
              --                $$ vcat(map (text . show) gs))
              traceTCM 30 $ (text "  INFERRED GLOBAL DECL: "
                             $$ vcat(map prettyPrintTCM (filter (not . isConstr . namedValue) gs)))
              cs <- allConstraints
              traceTCM 15 $ prettyPrintTCM (filter (not . isConstr . namedValue) gs)
              traceTCM 15 $ (text $ "Constraints:" ++ show cs)
          typeCheckFile :: Verbosity -> [A.Declaration] -> TCM ()
          typeCheckFile verb ds =
            do setVerbosity verb
               forM_ ds typeCheckDecl
