{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses
  #-}

module Kernel.Fix where

import Control.Monad.Reader

import Syntax.Internal hiding (lift)
import qualified Syntax.Abstract as A
import Kernel.Conversion
import {-# SOURCE #-} Kernel.TypeChecking


instance Infer A.FixExpr (Term, Type) where
  infer (A.FixExpr _ num f tp body) =
    do (tp', s) <- infer tp
       _ <- isSort s
       (body', u) <- local (Bind f tp':) $ infer body
       b <- conversion tp' u
       unless b $ error $ "fix error " ++ show tp' ++ " == " ++ show u
       return (Fix num f [] tp' body', tp')
