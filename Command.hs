module Command where

import Abstract
import Parser

data Command = Definition Name Expr Expr
             | Axiom Name Expr
             | Check Expr
             | Load FilePath


