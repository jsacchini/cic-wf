{- cicminus
 - Copyright 2011-2015 by Jorge Luis Sacchini
 -
 - This file is part of cicminus.
 -
 - cicminus is free software: you can redistribute it and/or modify it under the
 - terms of the GNU General Public License as published by the Free Software
 - Foundation, either version 3 of the License, or (at your option) any later
 - version.

 - cicminus is distributed in the hope that it will be useful, but WITHOUT ANY
 - WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 - FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 - details.
 -
 - You should have received a copy of the GNU General Public License along with
 - cicminus. If not, see <http://www.gnu.org/licenses/>.
 -}

{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Parser Monad. Based on code from Agda

module CICwf.Syntax.ParseMonad where

import Control.Exception
import Data.Functor
import Data.Maybe
import Data.Typeable

import Control.Monad.Error
import Control.Monad.State

import CICwf.Syntax.Alex
import CICwf.Syntax.Position

newtype Parser a = P { unP :: StateT ParseState (Either ParseError) a }
                   deriving(Monad,
                            Functor,
                            MonadState ParseState,
                            MonadError ParseError)

-- | The parser environment indicates if we are checking the type of a fixpoint.
--   In such case, it is allowed to have starred identifiers
type ParseEnv = Bool

data ParseState = ParseState { lexerInput   :: AlexInput,
                               positionType :: Bool
                             }

data ParseError = ParseError { errPos :: Position,
                               errMsg :: String }
                  deriving(Show,Typeable)

instance Error ParseError where
  strMsg = ParseError noPos

instance Exception ParseError

data ParseResult a = ParseOk a
                   | ParseFail ParseError

parseError :: String -> Parser a
parseError = fail

parseErrorAt :: Position -> String -> Parser a
parseErrorAt p s = P $ lift $ Left $ ParseError p s

initState :: FilePath -> String -> ParseState
initState path s = ParseState { lexerInput = initInput path s,
                                positionType = False
                              }

parse :: Parser a -> Maybe String -> String -> ParseResult a
parse (P p) filename s =
  case runStateT p (initState f s) of
    Left e      -> ParseFail e
    Right (r,_) -> ParseOk r
  where
    f = fromMaybe "<interactive>" filename

starAllowed :: Parser Bool
starAllowed = positionType <$> get

allowStar :: Parser ()
allowStar = do st <- get
               put (st { positionType = True })

forbidStar :: Parser ()
forbidStar = do st <- get
                put (st { positionType = False })

getLexerInput :: Parser AlexInput
getLexerInput = lexerInput <$> get

putLexerInput :: AlexInput -> Parser ()
putLexerInput inp = do st <- get
                       put (st { lexerInput = inp })
