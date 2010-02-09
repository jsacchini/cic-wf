{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, PackageImports,
  GeneralizedNewtypeDeriving
  #-}
module Test where

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import Text.ParserCombinators.Parsec

import Syntax.Parser
import Syntax.Abstract
import Syntax.Scope
import Environment
import Syntax.Global

newtype TestM a = TestM { unTestM :: ReaderT [Name] (StateT GlobalEnv IO) a }
                  deriving(Monad, MonadReader [Name], MonadState GlobalEnv)
instance MonadGE TestM where
    lookupGE x = do g <- get 
                    return $ lookupEnv x g

gg = emptyEnv

runTestM :: TestM a -> IO (a, GlobalEnv)
runTestM = flip runStateT gg . 
           flip runReaderT [] .
           unTestM

testP xs = case runParser parseExpression () "" xs of
             Left err -> print err
             Right e -> do (t, _) <- runTestM $ scope e
                           print e
                           print t
           
