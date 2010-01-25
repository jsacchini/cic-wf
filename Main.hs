{-# LANGUAGE PackageImports #-}

module Main where

import Data.Char

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Text.ParserCombinators.Parsec

import System.Console.Readline

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import qualified Environment as E
import Command

-- infer0 :: Expr -> Result I.Term
infer0 = runInitialTCM . infer

lam = Lam noPos
sort = TSort noPos
bound = Bound noPos

tid :: Expr
tid = lam "A" (sort Box) (lam "x" (bound 0) (bound 0))

tk :: Expr 
tk = lam "A" (sort  Box) $ lam "B" (sort  Box) $
     lam "x" (bound 1) $ lam "y" (bound 1) (bound 1)

runCommParser :: String -> Either ParseError Command
runCommParser = runParser pCommand () "<interactive>"

parseAndExec :: String -> Result ()
parseAndExec s = case runCommParser s of
                   Left e -> liftIO $ putStrLn $ "Parsing Error:\n" ++ show e
                   Right c -> processCommand c


readEvalPrint :: Result ()
readEvalPrint = do xs <- liftIO $ readline "> "
                   case xs >>= return . dropWhile isSpace of
                     Nothing -> return ()
                     Just "exit" -> return ()
                     Just "print" -> do g <- get
                                        liftIO $ putStr $ showEnv (E.listEnv g)
                                        readEvalPrint
                     Just inp -> do liftIO $ addHistory inp
                                    parseAndExec inp
                                    readEvalPrint
                where showEnv :: [(Name, E.Global)] -> String
                      showEnv = foldr (\x r -> x ++ "\n" ++ r) "" . map showG
                      showG (x, E.Def u t) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
                      showG (x, E.Axiom t) = "axiom " ++ x ++ " : " ++ show t

main :: IO ()
main = do r <- runInitialTCM readEvalPrint
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


