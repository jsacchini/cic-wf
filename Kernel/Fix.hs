{-# LANGUAGE PackageImports, FlexibleInstances, TypeSynonymInstances,
  GeneralizedNewtypeDeriving, FlexibleContexts, FunctionalDependencies,
  MultiParamTypeClasses,
  CPP
  #-}

module Kernel.Fix where

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


instance Infer A.FixExpr (Term, Type) where
  infer (A.FixExpr r num f tp body) =
    do (tp', s) <- infer tp
       s' <- isSort s
       (body', u) <- local (Bind f tp':) $ infer body
       b <- conversion tp' u
       unless b $ error $ "fix error " ++ show tp' ++ " == " ++ show u
       return $ (Fix num f [] tp' body', tp')
