{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}

module Main where

import System.Exit

import TopLevel.TopLevel
import TopLevel.Monad

main :: IO ()
main = do r <- runTLM $ runIM interactiveLoop
          case r of
            Right _ -> exitSuccess
            Left _ -> exitFailure
