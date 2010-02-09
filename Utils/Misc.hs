module Utils.Misc where

import Text.ParserCombinators.Parsec

parseEOF p = do e <- p
                eof
                return e
