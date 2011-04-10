module Syntax.Position where

import Data.Function
import System.FilePath

data Position = Pn { posFile :: FilePath,
                     posLine :: Int,
                     posCol :: Int }
                deriving(Eq)

data Range = Range { rStart, rEnd :: !Position }

class HasRange a where
  getRange :: a -> Range

instance Show Position where
   show (Pn path line col) = concat [path, ":", show line, ":", show col]
    -- show _ = ""

instance Show Range where
    -- show (Range start end) = concat [posFile start, ":",
    --                                  show (posLine start), ":",
    --                                  show (posCol start), "-",
    --                                  show (posLine end), ":",
    --                                  show (posCol end)]
    show _ = ""

instance HasRange Position where
  getRange p = Range p p

instance HasRange Range where
  getRange r = r

instance HasRange a => HasRange [a] where
  getRange [] = noRange
  getRange [x] = getRange x
  getRange (x:y:ys) = fuseRange (getRange x) (getRange (y:ys))

class HasRange t => SetRange t where
  setRange :: Range -> t -> t

instance SetRange Range where
  setRange = const

noPosFile :: FilePath -> Position
noPosFile f = Pn f 0 0

noPos :: Position
noPos = noPosFile ""

initPosFile :: FilePath -> Position
initPosFile f = Pn f 1 1

initPos :: Position
initPos = initPosFile ""

noRange :: Range
noRange = Range noPos noPos

noRangeFile :: FilePath -> Range
noRangeFile f = Range (noPosFile f) (noPosFile f)


movePos :: Position -> Char -> Position
movePos (Pn f l c) '\t' = Pn f l (((c+7) `div` 8)*8+1)
movePos (Pn f l c) '\n' = Pn f (l+1) 1
movePos (Pn f l c) _    = Pn f l (c+1)

advancePos :: Position -> Int -> Position
advancePos (Pn f l c) n = Pn f l (c + n)

mkRangeLen :: Position -> Int -> Range
mkRangeLen pos@(Pn f l c) n = Range pos (advancePos pos n)

-- Combines two ranges
-- Assumes that the first range is to the left of the second
fuseRange :: (HasRange a, HasRange b) => a -> b -> Range
fuseRange x y = Range posl posr
                where Range posl _ = getRange x
                      Range _ posr = getRange y

-- fuseRanges only works in non-empty lists
fuseRanges :: HasRange a => [a] -> Range
fuseRanges = foldr1 fuseRange . map getRange
