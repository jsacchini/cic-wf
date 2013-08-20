module Kernel.TCMErrors where

import Control.Monad.Reader

import Syntax.Position
import qualified Syntax.Internal as I

import Kernel.TCM
import Kernel.PrettyTCM

import Utils.Pretty

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

