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

-- | Code required for building the lexer using Alex

module CICwf.Syntax.Alex where

import CICwf.Syntax.Position

data AlexInput = AlexInput { lexPos :: Position,  -- ^ Current position
                             lexInput :: String,  -- ^ Current input
                             lexPrevChar :: Char  -- ^ Previous read character
                           }

type PreviousInput  = AlexInput
type CurrentInput   = AlexInput
type TokenLength    = Int

initInput :: FilePath -> String -> AlexInput
initInput path str = AlexInput (initPosFile path) str '\n'

-- alexInputPrevChar should not be needed since the lexer does not use patterns
-- with left-context. Otherwise, alexInputPrevChar = lexPrevChar
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = error "use of left-context rules not implemented"

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (AlexInput { lexInput = [] }) = Nothing
alexGetChar (AlexInput { lexPos = p, lexInput = c:s }) =
  Just (c, AlexInput { lexPos = movePos p c,
                       lexInput = s,
                       lexPrevChar = c })
