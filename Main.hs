{-# LANGUAGE PackageImports, TypeSynonymInstances, MultiParamTypeClasses #-}

module Main where

import Data.Char

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import qualified Control.Exception as E
import Text.ParserCombinators.Parsec

import System.Console.Haskeline
import System.Exit

import Position
import Abstract
import TCM
import qualified Internal as I
import Parser
import Typing
import qualified Environment as E
import Environment
import TopLevel

            
main :: IO ()
main = do r <- runTLM $ runIM interactiveLoop
          case r of
            Right _ -> exitSuccess
            Left _ -> exitFailure
                


