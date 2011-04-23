{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, FunctionalDependencies,
  MultiParamTypeClasses,
  CPP
  #-}

module Kernel.Case where

#include "../undefined.h"
import Utils.Impossible

import Control.Exception
import Control.Monad.Reader
import Control.Monad.Error

import Data.Function

import Syntax.Internal hiding (lift)
import Syntax.Internal as I
import Syntax.Common
import Syntax.Position
import qualified Syntax.Abstract as A
import Kernel.Conversion
import Kernel.TCM
import Kernel.Whnf
import {-# SOURCE #-} Kernel.TypeChecking


instance Infer A.CaseExpr (Term, Type) where
  infer (A.CaseExpr r arg asName inName sub ret branches) =
    error "typechecking of cAse to be implemented"
