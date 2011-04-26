{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable #-}
-- Parser Monad. Based on Agda

module Syntax.ParseMonad where

import Data.Functor
import Data.Typeable
import Control.Exception

import Control.Monad.State
import Control.Monad.Error

import Syntax.Position
import Syntax.Alex

newtype Parser a = P { unP :: StateT ParseState (Either ParseError) a }
                   deriving(Monad,
                            Functor,
                            MonadState ParseState,
                            MonadError ParseError)

-- | The parser environment indicates if we are checking the type of a fixpoint.
--   In such case, it is allowed to have starred identifiers
type ParseEnv = Bool

data ParseState = ParseState { lexerInput :: AlexInput,
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

parse :: Parser a -> String -> ParseResult a
parse (P p) s =
  case runStateT p (initState "<interactive>" s) of
    Left e      -> ParseFail e
    Right (r,_) -> ParseOk r

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

------------------------------------------------------------------------
-- Wrapping parse results
-- Stoled from Agda

wrap :: ParseResult a -> a
wrap (ParseOk x)     = x
wrap (ParseFail err) = throw err

wrapM:: Monad m => m (ParseResult a) -> m a
wrapM m =
  do r <- m
     case r of
       ParseOk x     -> return x
       ParseFail err -> throw err

------------------------------------------------------------------------
