{- cicminus
 - Copyright 2011 by Jorge Luis Sacchini
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

module Utils.Pretty where

import Text.PrettyPrint as PP

class Pretty a where
  prettyPrint :: a -> Doc
  prettyPrintDec :: Int -> a -> Doc

  prettyPrint = prettyPrintDec 0
  prettyPrintDec = const prettyPrint

instance Pretty Doc where
  prettyPrint = id

-- instance Pretty a => Pretty (Maybe a) where
--   prettyPrint = maybe empty prettyPrint
maybePPrint :: (Pretty a) => (a -> Doc) -> Maybe a -> Doc
maybePPrint = maybe empty


parensIf :: Bool -> Doc -> Doc
parensIf True = PP.parens
parensIf False = id

dot :: Doc
dot = PP.char '.'

defEq :: Doc
defEq = PP.text ":="

doubleColon :: Doc
doubleColon = PP.text "::"

implies :: Doc
implies = PP.text "=>"

bar :: Doc
bar = PP.char '|'

arrow :: Doc
arrow = PP.text "->"

langle :: Doc
langle = PP.char '<'

rangle :: Doc
rangle = PP.char '>'
