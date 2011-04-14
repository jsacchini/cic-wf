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
