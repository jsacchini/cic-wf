module Utils.Pretty where

import Text.PrettyPrint as PP

class Pretty a where
  prettyPrint :: a -> Doc
  prettyPrintDec :: Int -> a -> Doc

  prettyPrint = prettyPrintDec 0
  prettyPrintDec = const prettyPrint

instance Pretty Doc where
  prettyPrint = id

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
