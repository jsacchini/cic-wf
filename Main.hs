module Main where

import Prelude hiding (catch)

import System.IO

import System

import Control.Monad.Trans
import Control.Monad.State

import qualified Syntax.Abstract as A
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope

import Utils.Pretty

import Kernel.TCM
import Kernel.TypeChecking
import Syntax.InternaltoAbstract

main :: IO ()
main =
  do hSetBuffering stdout NoBuffering
     args <- getArgs
     mapM_ runFile args
    where runFile f =
            do h <- openFile f ReadMode
               ss <- hGetContents h
               case parse fileParser ss of
                 ParseOk ts ->
                   do print $ prettyPrint ts
                      r <- runTCM $ typeCheckFile ts
                      case r of
                        Left err -> putStrLn $ "Error!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d = do d' <- scope d
                               gs <- inferDecl d'
                               forM_ gs (uncurry addGlobal)
          typeCheckFile :: [A.Declaration] -> TCM ()
          typeCheckFile ds =
            do forM_ ds typeCheckDecl
