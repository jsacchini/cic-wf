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

import Utils.Misc

class (Functor gm,
       MonadIO gm,
       LookupName Global gm,
       ExtendName Global gm) => TCGlobalMonad gm where

data CommandError = AlreadyDefined Name
                    deriving(Typeable, Show)

instance Exception CommandError

alreadyDefined :: (TCGlobalMonad gm) => Name -> gm ()
alreadyDefined = liftIO . throwIO . AlreadyDefined

instance (TCGlobalMonad gm) => MonadTCM (ReaderT TCEnv gm) where

instance (TCGlobalMonad gm) => S.ScopeMonad (ReaderT [Name] gm) where

infer :: (TCGlobalMonad gm) => A.Expr -> gm (Term, Type)
infer = flip runReaderT [] . T.infer

check :: (TCGlobalMonad gm) => A.Expr -> Term -> gm Term
check e = flip runReaderT []  . T.check e

isSort :: (TCGlobalMonad gm) => Term -> gm Sort
isSort = flip runReaderT [] . T.isSort

scope :: (S.Scope a, TCGlobalMonad gm) => a -> gm a
scope = flip runReaderT [] . S.scope

scopeSub :: (S.Scope a, TCGlobalMonad gm) => [Name] -> a -> gm a
scopeSub xs = flip runReaderT xs . S.scope

normalForm :: (W.NormalForm a, TCGlobalMonad gm) => a -> gm a
normalForm = flip runReaderT [] . W.normalForm


checkCommand :: (TCGlobalMonad gm) => A.Command -> gm ()
checkCommand c = do c1 <- scope c
                    case c1 of
                      A.Definition x t u -> processDef x t u
                      A.AxiomCommand x t -> processAxiom x t
                      A.Load xs -> processLoad xs

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

addGlobal :: (TCGlobalMonad gm) => Name -> Global -> gm ()
addGlobal x g = do mWhen (definedName x) $ alreadyDefined x
                   extendName x g
