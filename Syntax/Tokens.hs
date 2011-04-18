module Syntax.Tokens where

import Syntax.Position

-- Keywords. Type is separated, since it has an argument
data Keyword = KwForall | KwFun | KwProp | KwLet | KwDefine | KwImport
             | KwAssume | KwRefine | KwMatch | KwAs | KwIn | KwReturn | KwWith
             | KwEnd | KwData | KwFix
             deriving(Eq,Show)

data Symbol = SymbLeftParen | SymbRightParen | SymbArrow | SymbImplies
            | SymbComma | SymbColonEq | SymbDot | SymbColon | SymbDoubleColon
            | SymbBar | SymbPos | SymbNeg | SymbSPos | SymbNeut
            deriving(Eq,Show)

-- TokType and TokIdent have a pair argument because Happy would only allows
-- us to access one argument of a token
data Token = TokKeyword Keyword Position
           | TokSymbol Symbol Position
           | TokType (Position,Int)
           | TokIdent (Position,String)
           | TokEOF
           deriving (Eq,Show)

-- keyword :: (Position -> Token) -> Position -> String -> Token
-- keyword k p _ = k p

typeKeyword :: Position -> String -> Token
typeKeyword p s = TokType (p, read $ drop 4 s)

symbol :: (Position -> String -> Token)
symbol p s =
  case lookup s symbolList of
    Just c -> TokSymbol c p
    Nothing -> error "Lexer error: symbol not found"
  where symbolList = [("(" , SymbLeftParen),
                      (")" , SymbRightParen),
                      ("->", SymbArrow),
                      ("=>", SymbImplies),
                      ("," , SymbComma),
                      (":=", SymbColonEq),
                      ("." , SymbDot),
                      (":" , SymbColon),
                      ("::", SymbDoubleColon),
                      ("|" , SymbBar),
                      ("+" , SymbPos),
                      ("-" , SymbNeg),
                      ("++", SymbSPos),
                      ("@" , SymbNeut)]

ident :: Position -> String -> Token
ident p s =
  case lookup s identList of
    Just c -> c p
    Nothing -> TokIdent (p,s)
  where identList = [("forall", TokKeyword KwForall),
                     ("fun"   , TokKeyword KwFun),
                     ("Type"  , \p -> TokType (p,0)), -- with no number
                     ("Prop"  , TokKeyword KwProp),
                     ("define", TokKeyword KwDefine),
                     ("let"   , TokKeyword KwLet),
                     ("import", TokKeyword KwImport),
                     ("assume", TokKeyword KwAssume),
                     ("match" , TokKeyword KwMatch),
                     ("as"    , TokKeyword KwAs),
                     ("in"    , TokKeyword KwIn),
                     ("return", TokKeyword KwReturn),
                     ("with"  , TokKeyword KwWith),
                     ("end"   , TokKeyword KwEnd),
                     ("data"  , TokKeyword KwData),
                     ("fix"   , TokKeyword KwFix)]
