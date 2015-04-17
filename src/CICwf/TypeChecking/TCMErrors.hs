module CICwf.TypeChecking.TCMErrors where

import Control.Monad.Reader

import CICwf.Syntax.Common
import CICwf.Syntax.Position
import qualified CICwf.Syntax.Internal as I
import qualified CICwf.Utils.Pretty as PP

import CICwf.TypeChecking.TCM
import CICwf.TypeChecking.PrettyTCM


prettyError :: (MonadTCM tcm) => TCErr -> tcm ()
prettyError (TypeError rg env err) = do
  d <- withEnv env $ vcat [ prettyTCM rg <> text ":"
                          , text "in context"
                          , prettyTCM env
                          , text "------"
                          , prettyTCM err ]
  liftIO $ print d
prettyError (ScopeError rg err) = do
  d <- hsep [ prettyTCM rg <> text ":"
            , prettyTCM err ]
  liftIO $ print d
