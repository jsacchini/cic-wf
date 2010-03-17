{-# LANGUAGE PackageImports, FlexibleContexts, FlexibleInstances,
  DeriveDataTypeable #-}
module Kernel.Command where

import "mtl" Control.Monad.Trans
import "mtl" Control.Monad.Reader
import Control.Exception

import Data.Foldable hiding (forM_)
import Data.Typeable

import System.IO

import qualified Syntax.Abstract as A
import Syntax.Global
import Syntax.Name
import Syntax.Internal
import Syntax.Parser
import qualified Syntax.Scope as S

import Kernel.TCM
import qualified Kernel.TypeChecking as T
import qualified Kernel.Whnf as W
import Kernel.GlobalMonad
import Kernel.Inductive

import Utils.Misc


checkCommand :: (TCGlobalMonad gm) => A.Command -> gm ()
checkCommand c = do c1 <- scope c
                    case c1 of
                      A.Definition x t u -> processDef x t u
                      A.AxiomCommand x t -> processAxiom x t
                      A.Load xs -> processLoad xs
                      A.Inductive i -> processInd i

processLoad :: (TCGlobalMonad gm) => FilePath -> gm ()
processLoad xs = do h <- liftIO $ openFile xs ReadMode
                    ss <- liftIO $ hGetContents h
                    cs <- runParser xs parseFile ss
                    liftIO $ hClose h
                    forM_ cs checkCommand

processAxiom :: (TCGlobalMonad gm) => Name -> A.Expr -> gm ()
processAxiom x t = do (t',r) <- infer t
                      isSort r
                      addGlobal x (Axiom t')

processDef :: (TCGlobalMonad gm) => Name -> Maybe A.Expr -> A.Expr -> gm ()
processDef x (Just t) u = do (t', r) <- infer t
                             isSort r
                             u' <- check u t'
                             addGlobal x (Def t' u')
processDef x Nothing u = do (u', r) <- infer u
                            addGlobal x (Def r u')
