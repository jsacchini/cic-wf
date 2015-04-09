module CICwf.TypeChecking.TCMErrors where

import Control.Monad.Reader

import CICwf.Syntax.Common
import CICwf.Syntax.Position
import qualified CICwf.Syntax.Internal as I
import qualified CICwf.Utils.Pretty as PP

import CICwf.TypeChecking.TCM
import CICwf.TypeChecking.PrettyTCM

-- throwNotConvertible :: (MonadTCM tcm) => Maybe Range -> I.Term -> I.Term -> tcm a
-- throwNotConvertible rg t u =
--   do
--     e <- ask
--     traceTCM 1 $ vcat [ text "NOT CONVERTIBLE" <+> prettyTCM rg
--                       , text "in CONTEXT" $$ (ask >>= prettyTCM)
--                       , text "==============================="
--                       , prettyTCM t
--                       , text "and"
--                       , prettyTCM u
--                       ]
--     typeError $ NotConvertible rg e t u


-- throwNotSort :: (MonadTCM tcm) => Range -> I.Term -> tcm a
-- throwNotSort rg s =
--   do
--     e <- ask
--     traceTCM 1 $ vcat [ text "NOT SORT" <+> prettyTCM rg
--                       , text "in CONTEXT" $$ (ask >>= prettyTCM)
--                       , text "==============================="
--                       , prettyTCM s
--                       ]
--     typeError $ NotSort rg e s


-- throwBranchPatternNotConvertible :: (MonadTCM tcm) => Range -> I.Context -> I.Context -> tcm a
-- throwBranchPatternNotConvertible rg c1 c2 =
--   do
--     e <- ask
--     traceTCM 1 $ vcat [ text "NOT CONVERTIBLE" <+> prettyTCM rg
--                       , text "in CONTEXT" $$ (ask >>= prettyTCM)
--                       , text "==============================="
--                       , prettyTCM c1
--                       , text "and"
--                       , prettyTCM c2
--                       ]
--     typeError $ BranchPatternNotConvertible rg c1 c2



-- -- Scope errors

-- wrongArg :: (MonadTCM tcm) => Range -> Name -> Int -> Int -> tcm a
-- wrongArg r x m n = typeError $ WrongNumberOfArguments r x m n

-- undefinedName :: (MonadTCM tcm) => Range -> Name -> tcm a
-- undefinedName r x = typeError $ UndefinedName r x

-- constrNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
-- constrNotApplied r x = typeError $ ConstructorNotApplied r x

-- inductiveNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
-- inductiveNotApplied r x = typeError $ InductiveNotApplied r x


-- failIfDefined :: (MonadTCM tcm) => Name -> tcm ()
-- failIfDefined x = isGlobal x >>= flip when (typeError (AlreadyDefined x))


-- notImplemented :: (MonadTCM tcm) => Range -> String -> tcm a
-- notImplemented rg s = typeError $ NotImplemented rg s

prettyError :: (MonadTCM tcm) => TCErr -> tcm ()
prettyError (TypeError rg env err) = do
  d <- vcat [ prettyTCM rg <> text ":"
            , text "in context"
            , prettyTCM env
            , text "------"
            , prettyTCM err ]
  liftIO $ print d
prettyError (ScopeError rg err) = do
  d <- hsep [ prettyTCM rg <> text ":"
            , prettyTCM err ]
  liftIO $ print d
