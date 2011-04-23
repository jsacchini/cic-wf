{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}

module Main where

import Prelude hiding (catch)

-- import System.Console.Haskeline
import System.IO

-- import Utils.MonadUndo
-- import Kernel.TCM
-- import Kernel.Command
-- import Kernel.GlobalMonad
-- import qualified Syntax.Internal as I
-- import Syntax.Parser
-- import Syntax.Global
-- import Syntax.Name
-- import qualified Kernel.TypeChecking as T
-- import qualified Kernel.GlobalMonad as GM
-- import qualified Environment as E
-- import Utils.Fresh
-- import Utils.Misc

import System
import System.Exit

import Control.Monad.Trans
import Control.Monad.State

-- import TopLevel.TopLevel
-- import TopLevel.Monad

import qualified Syntax.Abstract as A
import qualified Syntax.Internal as I
import Syntax.Lexer
import Syntax.Common
import Syntax.Tokens
import Syntax.ParseMonad
import Syntax.Parser
import Syntax.Scope

import Utils.Pretty

import Kernel.TCM
import Kernel.TypeChecking
import Syntax.InternaltoAbstract

import Control.Monad

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
                   do putStrLn $ show $ prettyPrint ts
                      putStrLn "---------------------"
                      r <- runTCM $ typeCheckFile ts
                      case r of
                        Left err -> putStrLn $ "Error!!!! " ++ show err
                        Right _ -> return ()
                 ParseFail err -> putStrLn $ "Error (Main.hs): " ++ show err
               hClose h
          parseTokens :: Parser [Token]
          parseTokens = do t <- lexToken
                           case t of
                             TokEOF -> return []
                             t' -> do ts <- parseTokens
                                      return (t':ts)
          typeCheckDecl :: A.Declaration -> TCM ()
          typeCheckDecl d = do d' <- scope d
                               liftIO $ putStrLn $ "scoped " ++ show d'
                               gs <- infer d'
                               forM_ gs (uncurry addGlobal)
          typeCheckFile :: [A.Declaration] -> TCM ()
          typeCheckFile ds =
            do forM_ ds typeCheckDecl
               liftIO $ putStrLn "========================"
               sig <- fmap stSignature get
               liftIO $ putStrLn "========================"
               liftIO $ putStrLn $ show sig
               liftIO $ putStrLn "========================"
               xs <- fmap stDefined get
               forM_ xs showG
                 where showG x = do d <- reify x
                                    liftIO $ putStrLn $ (show $  prettyPrint d) ++  "\n----\n" ++ show d ++ "\n===="

-- main2 :: IO ()
-- main2 =
--   do args <- getArgs
--      mapM_ runFile args
--   where runFile f = do r <- runTLM (processFile f)
--                        case r of
--                          Left e -> putStrLn $ show e
--                          Right _ -> return ()
--         processFile f = do h <- liftIO $ openFile f ReadMode
--                            ss <- liftIO $ hGetContents h
--                            cs <- runParser f parseFile ss
--                            liftIO $ hClose h
--                            liftIO $ putStrLn $ concat $ ["\n-----------\n", f, "\n-----------"]
--                            forM_ cs checkCommand
--         checkCommand :: (TCGlobalMonad gm) => A.Command -> gm ()
--         checkCommand c = do c1 <- scope c
--                             case c1 of
--                               A.Definition x t u -> processDef x t u
--                               A.AxiomCommand x t -> processAxiom x t
--                               _ -> throwIO $ InternalError "not implemented"
--         processAxiom :: (TCGlobalMonad gm) => Name -> A.Expr -> gm ()
--         processAxiom x t = do (t',r) <- infer t
--                               isSort r
--                               liftIO $ putStrLn $ concat $ ["Axiom ", x, ": ",show t',"  (: ",show r,")"]
--                               addGlobal x (Axiom t')

--         processDef :: (TCGlobalMonad gm) => Name -> Maybe A.Expr -> A.Expr -> gm ()
--         processDef x (Just t) u = do (t', r) <- infer t
--                                      isSort r
--                                      u' <- check u t'
--                                      liftIO $ putStrLn $ concat $ ["Def ", x, ": ", show t'," := ",show u']
--                                      addGlobal x (Def t' u')
--         processDef x Nothing u = do (u', t') <- infer u
--                                     liftIO $ putStrLn $ concat $ ["Def ", x, ": ", show t'," := ",show u']
--                                     addGlobal x (Def t' u')
