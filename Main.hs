{-# LANGUAGE PackageImports #-}

module Main where

import System.Console.Readline
import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import Environment


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

-- test :: String -> IO ()
-- test s = case tempParse s of
--            Left e -> putStrLn $ "Parsing Error: " ++ show e
--            Right t -> do r <- infer0 t
--                            print r


inferAddGlobal :: String -> Result ()
inferAddGlobal s = case tempParse' parseLet s of
                     Left e -> liftIO $ putStrLn $ "Parsing Error:\n" ++ show e
                     Right (x, t) -> do r <- infer t
                                        g <- get
                                        liftIO $ print r
                                        put (extendEnv x (Def (I.interp t) r) g)
                                     `catchError` \err -> liftIO $ putStrLn $ "Typing Error:\n" ++ show err


readEvalPrint :: Result ()
readEvalPrint = do xs <- liftIO $ readline "> "
                   case xs of
                     Nothing -> return ()
                     Just "exit" -> return ()
                     Just "print" -> do g <- get
                                        liftIO $ putStr $ showEnv (listEnv g)
                                        readEvalPrint
                     Just inp -> do liftIO $ addHistory inp
                                    inferAddGlobal inp
                                    readEvalPrint
                where showEnv :: [(Name, Global)] -> String
                      showEnv = foldr (\x r -> x ++ "\n" ++ r) "" . map showG
                      showG (x, Def u t) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show u
                      showG (x, Axiom t) = "axiom " ++ x ++ " : " ++ show t

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


