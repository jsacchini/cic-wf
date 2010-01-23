module Main where

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import Environment


infer0 :: Expr -> Result I.Term
infer0 = infer emptyGlobal emptyLocal

lam = Lam noPos
sort = TSort noPos
bound = Bound noPos

tid :: Expr
tid = lam "A" (sort Box) (lam "x" (bound 0) (bound 0))

tk :: Expr 
tk = lam "A" (sort  Box) $ lam "B" (sort  Box) $
     lam "x" (bound 1) $ lam "y" (bound 1) (bound 1)

test :: String -> IO ()
test s = case tempParse s of
           Left e -> print "Parsing Error: " >> print e
           Right t -> print $ infer0 t

           

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

