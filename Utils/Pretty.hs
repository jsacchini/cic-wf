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

-- | Defines the class 'Pretty' for stuff that can be pretty-printed.

module Utils.Pretty where

import Text.PrettyPrint as PP

class Pretty a where
  prettyPrint :: a -> Doc
  prettyPrintDec :: Int -> a -> Doc

  prettyPrint = prettyPrintDec 0
  prettyPrintDec = const prettyPrint

instance Pretty Doc where
  prettyPrint = id

instance Pretty a => Pretty (Maybe a) where
  prettyPrint = maybe empty prettyPrint

parensIf :: Bool -> Doc -> Doc
parensIf True = PP.parens
parensIf False = id

dot, defEq, doubleColon, implies, bar, arrow, langle, rangle, comma :: Doc

dot         = PP.char '.'
defEq       = PP.text ":="
doubleColon = PP.text "::"
implies     = PP.text "=>"
bar         = PP.char '|'
arrow       = PP.text "->"
langle      = PP.char '<'
rangle      = PP.char '>'
comma       = PP.char ','
