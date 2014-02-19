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

-- | Tokens returned by the lexer.

module CICminus.Syntax.Tokens where

import Data.Maybe

import CICminus.Syntax.ParseMonad
import CICminus.Syntax.Position

data Keyword = KwForall | KwFun | KwProp | KwType | KwLet | KwDefine | KwImport
             | KwAssume | KwRefine | KwCase | KwAs | KwIn | KwReturn | KwWith
             | KwEnd | KwWhere | KwOf | KwEval | KwCheck
             | KwData | KwCodata
             | KwFix | KwCofix | KwStruct
             | KwFixpoint | KwCofixpoint
             | KwMeta | KwPrint
             deriving(Eq,Show)

data Symbol = SymbLeftParen | SymbRightParen | SymbLeftBrace | SymbRightBrace
            | SymbArrow | SymbImplies
            | SymbComma | SymbColonEq | SymbDot | SymbColon | SymbDoubleColon
            | SymbBar | SymbPos | SymbNeg | SymbSPos | SymbNeut
            | SymbStar
            | SymbLAngle | SymbRAngle | SymbLBracket | SymbRBracket
            deriving(Eq,Show)

-- TokIdent has a pair argument because Happy would only allows
-- us to access one argument of a token
data Token = TokKeyword Keyword Position
           | TokSymbol Symbol Position
           | TokFixNumber (Position, Int)
           | TokTypeNumber (Position, Int)
           | TokIdent (Position, String)
           | TokIdentStar (Position, String)
           | TokNumber (Position, Int)
           | TokEOF
           deriving (Eq,Show)

-- keyword :: (Position -> Token) -> Position -> String -> Token
-- keyword k p _ = k p

-- Below are the lexer actions of type Position -> String -> Parser Token

fixKeyword :: Position -> String -> Parser Token
fixKeyword p s = return $ TokFixNumber (p, read $ drop 3 (sub2Number s))

typeKeyword :: Position -> String -> Parser Token
typeKeyword p s = return $ TokTypeNumber (p, read $ drop 4 (sub2Number s))

sub2Number :: String -> String
sub2Number = map sub2Digit
  where sub2Digit c = fromMaybe c (lookup c subTable)
        subTable = zip (['\x2080'..'\x2089']++['0'..'9'])
                       (['0'..'9']++['0'..'9'])

number :: Position -> String -> Parser Token
number p s = return $ TokNumber (p, read (sub2Number s))

symbol :: Position -> String -> Parser Token
symbol p s =
  case lookup s symbolList of
    Just c  -> return $ TokSymbol c p
    Nothing -> error ("Lexer error" ++ show p ++ ": symbol not found")
  where symbolList =
          [ ("(" , SymbLeftParen)
          , (")" , SymbRightParen)
          , ("{" , SymbLeftBrace)
          , ("}" , SymbRightBrace)
          , ("->", SymbArrow)
          , ("=>", SymbImplies)
          , ("," , SymbComma)
          , (":=", SymbColonEq)
          , ("." , SymbDot)
          , (":" , SymbColon)
          , ("::", SymbDoubleColon)
          , ("|" , SymbBar)
          , ("+" , SymbPos)
          , ("-" , SymbNeg)
          , ("++", SymbSPos)
          , ("@" , SymbNeut)
          , ("*" , SymbStar)
          , ("<" , SymbLAngle)
          , (">" , SymbRAngle)
          , ("[" , SymbLBracket)
          , ("]" , SymbRBracket)
          ]

symbolOrOther :: Position -> String -> Parser Token
symbolOrOther p "\x03a0" = return $ TokKeyword KwForall p
symbolOrOther p "\x03bb" = return $ TokKeyword KwFun p
symbolOrOther p "\x2192" = return $ TokSymbol SymbArrow p
symbolOrOther p s        = symbol p s

identStar :: Position -> String -> Parser Token
identStar pos s = do tok <- ident pos (init s) -- remove the '*'
                     case tok of
                       TokIdent (p',s') -> return $ TokIdentStar (p',s')
                       _                -> fail "Lexical error tokstar"

ident :: Position -> String -> Parser Token
ident pos s =
  case lookup s identList of
    Just c  -> return $ c pos
    Nothing -> return $ TokIdent (pos,s)
  where identList =
          [ ("forall", TokKeyword KwForall)
          , ("\\"    , TokKeyword KwFun)
          , ("fun"   , TokKeyword KwFun)
          , ("Type"  , TokKeyword KwType)
          , ("Prop"  , TokKeyword KwProp)
          , ("define", TokKeyword KwDefine)
          , ("eval"  , TokKeyword KwEval)
          , ("check" , TokKeyword KwCheck)
          , ("print" , TokKeyword KwPrint)
          , ("let"   , TokKeyword KwLet)
          , ("import", TokKeyword KwImport)
          , ("assume", TokKeyword KwAssume)
          , ("case"  , TokKeyword KwCase)
          , ("as"    , TokKeyword KwAs)
          , ("in"    , TokKeyword KwIn)
          , ("return", TokKeyword KwReturn)
          , ("with"  , TokKeyword KwWith)
          , ("data"  , TokKeyword KwData)
          , ("codata", TokKeyword KwCodata)
          , ("fix"   , TokKeyword KwFix)
          , ("cofix" , TokKeyword KwCofix)
          , ("fixpoint"   , TokKeyword KwFixpoint)
          , ("cofixpoint" , TokKeyword KwCofixpoint)
          , ("struct", TokKeyword KwStruct)
          , ("where" , TokKeyword KwWhere)
          , ("of"    , TokKeyword KwOf)
          , ("end"   , TokKeyword KwEnd)
          , ("_"     , TokKeyword KwMeta)
          ]
