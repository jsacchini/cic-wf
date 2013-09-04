module TypeChecking.TCMErrors where

import Control.Monad.Reader

import Syntax.Common
import Syntax.Position
import qualified Syntax.Internal as I

import TypeChecking.TCM
import TypeChecking.PrettyTCM

throwNotConvertible :: (MonadTCM tcm) => Maybe Range -> I.Term -> I.Term -> tcm a
throwNotConvertible rg t u =
  do
    e <- ask
    traceTCM 1 $ vcat [ text "NOT CONVERTIBLE" <+> prettyPrintTCM rg
                      , text "in CONTEXT" $$ (ask >>= prettyPrintTCM)
                      , text "==============================="
                      , prettyPrintTCM t
                      , text "and"
                      , prettyPrintTCM u
                      ]
    typeError $ NotConvertible rg e t u


throwNotSort :: (MonadTCM tcm) => Range -> I.Term -> tcm a
throwNotSort rg s =
  do
    e <- ask
    traceTCM 1 $ vcat [ text "NOT SORT" <+> prettyPrintTCM rg
                      , text "in CONTEXT" $$ (ask >>= prettyPrintTCM)
                      , text "==============================="
                      , prettyPrintTCM s
                      ]
    typeError $ NotSort rg e s


-- Scope errors

wrongArg :: (MonadTCM tcm) => Range -> Name -> Int -> Int -> tcm a
wrongArg r x m n = typeError $ WrongNumberOfArguments r x m n

undefinedName :: (MonadTCM tcm) => Range -> Name -> tcm a
undefinedName r x = typeError $ UndefinedName r x

constrNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
constrNotApplied r x = typeError $ ConstructorNotApplied r x

inductiveNotApplied :: (MonadTCM tcm) => Range -> Name -> tcm a
inductiveNotApplied r x = typeError $ InductiveNotApplied r x


failIfDefined :: (MonadTCM tcm) => Name -> tcm ()
failIfDefined x = isGlobal x >>= flip when (typeError (AlreadyDefined x))
