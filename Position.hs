module Position where

import Text.ParserCombinators.Parsec.Pos

data Position = Position { pStart, pEnd :: SourcePos }
                
instance Show Position where
    show _ = ""

noPosFile :: SourceName -> Position
noPosFile f = Position (newPos f 0 0) (newPos f 0 0)

noPos :: Position
noPos = noPosFile ""

mkPos :: SourcePos -> SourcePos -> Position
mkPos = Position