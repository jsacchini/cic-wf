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

import           Control.Monad.Catch
import           Control.Monad.State

-- import qualified Text.PrettyPrint          as PP

import           CICwf.Syntax.AbstractToConcrete
import qualified CICwf.Syntax.Concrete           as C
import           CICwf.Syntax.ParseMonad
import           CICwf.Syntax.Parser
import           CICwf.Syntax.Scope

-- import qualified CICwf.TypeChecking.Constraints  as CS
import           CICwf.TypeChecking.Declaration
import           CICwf.TypeChecking.PrettyTCM
import           CICwf.TypeChecking.TCM
import           CICwf.TypeChecking.TCMErrors

-- import           CICwf.TopLevel.Monad
-- import           CICwf.TopLevel.TopLevel


data Options =
  Options { optVerbose :: Int -- Verbosity
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
               do -- putStrLn "OK"
                  -- putStrLn $ show ts
                  -- mapM_ (\x -> putStrLn (show x ++ "\n---------")) ts
                  -- putStrLn "===================\n=================\n\n"
                  -- r <- runTCM $ printAll ts
                   r <- runTCMIO (typeCheckFile (optVerbose opts) ts
                                  `catch` printError)
                   case r of
                     Right _ -> exitSuccess
                     Left _  -> exitFailure
                  -- _ <- runTCMIO $ do
                  --   r <- runTCM $ typeCheckFile (optVerbose opts) ts
                  --   case r of
                  --     Left err -> dputStrLn ("Error!!!! " ++ show err)
                  --     Right _ -> putStrLn "OK"
             ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
           hClose h
      printError :: (MonadTCM tcm) => TCErr -> tcm ()
      printError err = do
        prettyError err
        throwM err


      typeCheckDecl :: C.Declaration -> TCM ()
      typeCheckDecl d =
        do
          traceTCM 50 $ hsep [ text "  SCOPE GLOBAL DECL: "
                             , prettyTCM d ]
          d' <- scope d
          consc <- concretize d'
          traceTCM 50 $ hsep [ text "  INFER GLOBAL DECL: "
                             , prettyTCM consc ]
          inferDecl d'
          -- traceTCM 30 $ (text "  INFERRED GLOBAL DECL: (SHOW)"
          --                $$ vcat(map (text . show) gs))
          cs <- allConstraints
          -- traceTCM 15 $ prettyTCM (filter (not . I.isConstr . namedValue) gs)
          traceTCM 3 $ (text $ "Constraints:" ++ show cs)
          wfcs <- getWfConstraints
          -- traceTCM 15 $ prettyTCM (filter (not . I.isConstr . namedValue) gs)
          traceTCM 3 $ (text "Wf-Constraints:" <+> vcat (map prettyTCM wfcs))
      typeCheckFile :: Verbosity -> [C.Declaration] -> TCM ()
      typeCheckFile verb ds =
        do setVerbosity verb
           forM_ ds typeCheckDecl
