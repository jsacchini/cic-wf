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

-- | Defines the class 'Pretty' for stuff that can be pretty-printed.


module CICminus.Utils.Pretty
       ( module Text.PrettyPrint.ANSI.Leijen
       , module CICminus.Utils.Pretty
       ) where

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.PrettyPrint.ANSI.Leijen hiding (Pretty,pretty)


class Pretty a where
  pretty    :: a -> Doc
  prettyDec :: Int -> a -> Doc

  pretty = prettyDec 0
  prettyDec = const pretty


instance Pretty a => Pretty [a] where
  pretty = list . map pretty

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing = empty
  pretty (Just x) = pretty x

instance Pretty Doc where
  pretty = id

instance Pretty () where
  pretty () = text "()"

instance Pretty Bool where
  pretty = bool

instance Pretty Char where
  pretty = char

instance Pretty Int where
  pretty = int

instance Pretty Integer where
  pretty = integer



parensIf :: Bool -> PP.Doc -> PP.Doc
parensIf True = PP.parens
parensIf False = id

defEq, doubleColon, implies, bar, arrow :: Doc

defEq       = PP.text ":="
doubleColon = PP.text "::"
implies     = PP.text "=>"
bar         = PP.char '|'
arrow       = PP.text "->"

($$) :: Doc -> Doc -> Doc
($$) = (<$$>)
