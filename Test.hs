{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies, PackageImports,
  GeneralizedNewtypeDeriving
  #-}
module Test where

import "mtl" Control.Monad.Reader
import "mtl" Control.Monad.State
import Text.ParserCombinators.Parsec

import System.IO

import Syntax.Bind
import Syntax.Name
import Syntax.Parser
import Syntax.Abstract
import qualified Syntax.Internal as I
import Syntax.Scope
import Environment
import Syntax.Global

newtype TestM a = TestM { unTestM :: ReaderT [Name] (StateT GlobalEnv IO) a }
                  deriving(Monad, MonadReader [Name], MonadState GlobalEnv, MonadIO)
instance MonadGE TestM where
    lookupGE x = do g <- get
                    return $ lookupEnv x g
    toListGE = do g <- get
                  return $ listEnv g
    extendGE x a = do g <- get
                      put (extendEnv x a g)

gg = foldr (uncurry extendEnv) emptyEnv
     [("list", list),
      ("nat", nat),
      ("O", zero),
      ("S", suc)]

nat = IndDef [] [] I.Box
      [MkConstr "O" [] [],
       MkConstr "S" [NoBind $ I.Bound 0] []]

zero = ConstrDef ("nat",0) [] [] I.Box [] []
suc = ConstrDef ("nat",1) [] [] I.Box [NoBind $ I.Bound 0] []

list = IndDef [Bind "A" (I.TSort I.Box)] [] I.Box
       [MkConstr "nil" [] [],
        MkConstr "cons" [NoBind $ I.Bound 0, NoBind $ I.Bound 1] []]

runTestM :: TestM a -> IO (a, GlobalEnv)
runTestM = flip runStateT gg .
           flip runReaderT [] .
           unTestM

testS xs = case runParser parseExpr () "" xs of
             Left err -> print err
             Right e -> do (t, _) <- runTestM $ scope e
                           print e
                           print t

testP xs = case runParser parseExpr () "" xs of
             Left err -> print err
             Right e -> print e

testF xs = do h <- openFile xs ReadMode
              ss <- hGetContents h
              case runParser parseFile () xs ss of
                Left err -> print err
                Right e -> print e
              hClose h
