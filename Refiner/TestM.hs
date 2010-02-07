module Refiner.TestM where

import Refiner.Refiner
import Refiner.Internal
import Refiner.RM
import Abstract
import Position
import Parser
import Text.ParserCombinators.Parsec

unRight (Right x) = x

testRM = runRM . refine . unRight . runParser (parseExpr True) () "" 