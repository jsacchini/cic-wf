-- code required by Alex

module Syntax.Alex where

import Syntax.Position

data AlexInput = AlexInput { lexPos :: Position,  -- current position
                             lexInput :: String,  -- current input
                             lexPrevChar :: Char  -- previous read character
                           }

initInput :: FilePath -> String -> AlexInput
initInput path str = AlexInput (initPosFile path) str '\n'

-- alexInputPrevChar should not be needed since the lexer does not use patterns
-- with left-context. Otherwise, just return lexPrevChar
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = error "use of left-context rules not implemented"


alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (AlexInput { lexInput = [] }) = Nothing
alexGetChar (AlexInput { lexPos = p, lexInput = c:s }) = 
  Just (c, AlexInput { lexPos = movePos p c,
                       lexInput = s,
                       lexPrevChar = c })
