{-# LANGUAGE PackageImports, TypeSynonymInstances, MultiParamTypeClasses #-}

module Main where

import Data.Char

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import qualified Environment as E
import Command
import Environment

-- | Interaction monad.

type IM = TCM (InputT IO)

instance MonadError TCErr IM where
  throwError = liftIO . throwIO
  catchError m h = mapTCMT liftIO $ runIM m `catchError` (runIM . h)

-- | Line reader. The line reader history is not stored between
-- sessions.

readline :: String -> IM (Maybe String)
readline = lift . getInputLine

runIM :: IM a -> Result a
runIM = mapTCMT (runInputT defaultSettings)

-- runCommParser :: String -> Either ParseError Command
-- runCommParser = runParser parseFile () "<interactive>"

-- parseAndExec :: String -> Result ()
-- parseAndExec s = case runCommParser s of
--                    Left e -> liftIO $ putStrLn $ "Parsing Error:\n" ++ show e
--                    Right c -> processCommand c

-- runrun3 :: String -> IO (Either TCErr ())
-- runrun3 s = (runTCM $ parseAndExec s) --`E.catch` (\x -> putStrLn (show x))
-- runrun3 :: String -> Result Command
-- runrun3 = liftIO . runrun pCommand

processCommand :: Command -> Result ()
processCommand (Definition x t u) = processDef x t u

processDef :: Name -> Maybe Expr -> Expr -> Result ()
processDef x (Just t) u = do check u (I.interp t)
                             g <- get
                             put (extendEnv x (Def (I.interp u) (I.interp t)) g)
processDef x Nothing u = do r <- infer u
                            g <- get
                            put (extendEnv x (Def (I.interp u) r) g)

parseAndExec :: String -> Result ()
parseAndExec s = do c <-liftIO $ runParserIO parseCommand s
                    processCommand c

rvp :: Result () -> IM ()
rvp tc = liftTCM tt
         where tt = tc `catchError` \e -> liftIO (putStrLn (show e))
            
            

-- readEvalPrint :: Result ()
-- readEvalPrint :: IM ()
readEvalPrint = loop
    where loop :: IM ()
          loop =
                do xs <- readline "> "
                   case fmap (dropWhile isSpace) xs of
                     Nothing -> return ()
                     Just "" -> loop
                     Just "exit" -> return ()
                     Just "print" -> do g <- get
                                        lift $ outputStr $ showEnv (E.listEnv g)
                                        readEvalPrint
                     Just inp -> do -- liftIO $ addHistory inp
                                    -- liftTCM $ parseAndExec inp
                                    rvp $ parseAndExec inp
                                    readEvalPrint
--                `catchError` \e -> ( lift $ outputStr (show e)) >> loop
                where showEnv :: [(Name, E.Global)] -> String
                      showEnv = foldr ((\x r -> x ++ "\n" ++ r) . showG) ""
                      showG (x, E.Def u t) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
                      showG (x, E.Axiom t) = "axiom " ++ x ++ " : " ++ show t

main :: IO ()
main = do r <- runTCM $ runIM readEvalPrint
          print r
                


-- g_nat = Ind [] [] Box [("O", [], []), ("S", [("",bound0)], [])]
-- g_vec = Ind [("A",sort Box)] [("",Free "nat")] Box 
--             [("nil", [], [Constr "O" [] []]),
--              ("cons", [("n", Free "nat"), 
--                        ("", bound1), -- 
--                        ("", mapp (bound3) [bound2, bound1])],
--               [App (Free "S") (bound2)])]
                       
                                               

-- g1 = MkGE [("nat", g_nat), ("vec", g_vec), 
--            ("A", Axiom (sort Box)),("x", Axiom (Free "A"))]

-- infer1 = infer g1 []


