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
