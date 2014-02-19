{-
Copyright (c) 2005-2011 Ulf Norell, Nils Anders Danielsson, Catarina
Coquand, Makoto Takeyama, Andreas Abel, Karl Mehltretter, Marcin
Benke, Darin Morrison.

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

------------------------------------------------------------------------
-- | An interface for reporting \"impossible\" errors
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}

module CICminus.Utils.Impossible where

import qualified Control.Exception as E(Exception,throw,catch,assert)
import Data.Typeable

-- | \"Impossible\" errors, annotated with a file name and a line
-- number corresponding to the source code location of the error.

data Impossible = Impossible String Integer deriving Typeable

instance Show Impossible where
  show (Impossible file line) = unlines
    [ "An internal error has occurred. Please report this as a bug."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]

instance E.Exception Impossible

-- | Abort by throwing an \"impossible\" error. You should not use
-- this function directly. Instead use the macro in @undefined.h@.

throwImpossible :: Impossible -> a
throwImpossible = E.throw

-- | Catch an \"impossible\" error, if possible.

catchImpossible :: IO a -> (Impossible -> IO a) -> IO a
catchImpossible = E.catch

__IMPOSSIBLE__ :: a
__IMPOSSIBLE__ = E.assert False undefined
