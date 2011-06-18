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

-- main :: IO ()
-- main = do r <- runTLM $ runIM interactiveLoop
--           case r of
--             Right _ -> exitSuccess
--             Left _ -> exitFailure

-- instance MonadIO TCM

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
                      putStrLn "---------------------"
                      r <- runTCM $ typeCheckFile ts
                      case r of
                        Left err -> putStrLn $ "Error!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
               putStrLn "\n *** FIN ***"
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d = do d' <- scope d
                               traceTCM $ "Scoped " ++ (show $ prettyPrint d')
                               gs <- inferDecl d'
                               -- st <- getSignature
                               -- liftIO $ putStrLn $ show st
                               forM_ gs (uncurry addGlobal)
                               -- let xs = map fst gs
                               -- traceTCM_ ["Typed !! ", show xs]
                               -- traceTCM_ [show gs]
                               -- ds <- mapM reify xs
                               -- traceTCM_ ["Typed ", show (map prettyPrint ds)]
          typeCheckFile :: [A.Declaration] -> TCM ()
          typeCheckFile ds =
            do forM_ ds typeCheckDecl
               traceTCM "========================"
               -- st <- fmap stSignature get
               -- traceTCM $ show st
               -- traceTCM "========================"
               -- con <- fmap stConstraints get
               -- traceTCM $ show con
               -- traceTCM "========================"
               -- -- liftIO $ putStrLn "========================"
               -- -- liftIO $ print sig
               -- -- liftIO $ putStrLn "========================"
               -- xs <- fmap stDefined get
               -- forM_ xs showG
               --   where showG x = do d <- reify x
               --                      liftIO $ putStrLn $ show (prettyPrint d) ++  "\n----\n" ++ show d ++ "\n===="

