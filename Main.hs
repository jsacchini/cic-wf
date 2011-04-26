module Main where

import Prelude hiding (catch)

import System.IO

import System

import Control.Monad.Trans
import Control.Monad.State

import qualified Syntax.Abstract as A
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.ScopeMonad
import Syntax.Scope

import Utils.Pretty

import Kernel.TCM
import Kernel.TypeChecking
import Syntax.InternaltoAbstract

-- main :: IO ()
-- main = do r <- runTLM $ runIM interactiveLoop
--           case r of
--             Right _ -> exitSuccess
--             Left _ -> exitFailure

-- instance MonadIO TCM

main :: IO ()
main =
  do args <- getArgs
     mapM_ runFile args
    where runFile f =
            do h <- openFile f ReadMode
               ss <- hGetContents h
               case parse fileParser ss of
                 ParseOk ts ->
                   do print $ prettyPrint ts
                      putStrLn "---------------------"
                      r <- runTCM $ typeCheckFile ts
                      case r of
                        Left err -> putStrLn $ "\nError!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
               putStrLn "\n *** FIN ***"
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d = do d' <- runScopeM $ scope d
                               liftIO $ putStrLn $ "scoped " ++ show d'
                               gs <- infer d'
                               forM_ gs (uncurry addGlobal)
          typeCheckFile :: [A.Declaration] -> TCM ()
          typeCheckFile ds =
            do forM_ ds typeCheckDecl
               liftIO $ putStrLn "========================"
               sig <- fmap stSignature get
               liftIO $ putStrLn "========================"
               liftIO $ print sig
               liftIO $ putStrLn "========================"
               xs <- fmap stDefined get
               forM_ xs showG
                 where showG x = do d <- runScopeM $ reify x
                                    liftIO $ putStrLn $ show (prettyPrint d) ++  "\n----\n" ++ show d ++ "\n===="

