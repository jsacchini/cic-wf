-- | Tokens returned by the lexer.

module Syntax.Tokens where

import Syntax.Position
import Syntax.ParseMonad

-- Keywords. Type is separated, since it has an argument
data Keyword = KwForall | KwFun | KwProp | KwLet | KwDefine | KwImport
             | KwAssume | KwRefine | KwCase | KwAs | KwIn | KwReturn | KwWith
             | KwEnd | KwData | KwFix | KwWhere | KwOf | KwEval | KwCheck
             deriving(Eq,Show)

data Symbol = SymbLeftParen | SymbRightParen | SymbArrow | SymbImplies
            | SymbComma | SymbColonEq | SymbDot | SymbColon | SymbDoubleColon
            | SymbBar | SymbPos | SymbNeg | SymbSPos | SymbNeut
            | SymbLAngle | SymbRAngle | SymbLBracket | SymbRBracket
            deriving(Eq,Show)

-- TokType and TokIdent have a pair argument because Happy would only allows
-- us to access one argument of a token
data Token = TokKeyword Keyword Position
           | TokSymbol Symbol Position
           | TokType (Position, Int)
           | TokIdent (Position, String)
           | TokIdentStar (Position, String)
           | TokNumber (Position, Int)
           | TokEOF
           deriving (Eq,Show)

-- keyword :: (Position -> Token) -> Position -> String -> Token
-- keyword k p _ = k p

typeKeyword :: Position -> String -> Parser Token
typeKeyword p s = return $ TokType (p, read $ drop 4 s)

number :: Position -> String -> Parser Token
number p s = return $ TokNumber (p, read s)

symbol :: Position -> String -> Parser Token
symbol p s =
  case lookup s symbolList of
    Just c  -> return $ TokSymbol c p
    Nothing -> error "Lexer error: symbol not found"
  where symbolList =
          [("(" , SymbLeftParen),
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
           ("@" , SymbNeut),
           ("<" , SymbLAngle),
           (">" , SymbRAngle),
           ("[" , SymbLBracket),
           ("]" , SymbRBracket)]

identStar :: Position -> String -> Parser Token
identStar pos s = do tok <- ident pos (take (length s - 1) s) -- remove the '*'
                     case tok of
                       TokIdent (p',s') -> return $ TokIdentStar (p',s')
                       _                -> fail "Lexical error tokstar"

ident :: Position -> String -> Parser Token
ident pos s =
  case lookup s identList of
    Just c  -> return $ c pos
    Nothing -> return $ TokIdent (pos,s)
  where identList =
          [("forall", TokKeyword KwForall),
           ("fun"   , TokKeyword KwFun),
           ("Type"  , flip (curry TokType) 0), -- if Type has no number
           ("Prop"  , TokKeyword KwProp),
           ("define", TokKeyword KwDefine),
           ("eval"  , TokKeyword KwEval),
           ("check" , TokKeyword KwCheck),
           ("let"   , TokKeyword KwLet),
           ("import", TokKeyword KwImport),
           ("assume", TokKeyword KwAssume),
           ("case"  , TokKeyword KwCase),
           ("as"    , TokKeyword KwAs),
           ("in"    , TokKeyword KwIn),
           ("return", TokKeyword KwReturn),
           ("with"  , TokKeyword KwWith),
           ("data"  , TokKeyword KwData),
           ("fix"   , TokKeyword KwFix),
           ("where" , TokKeyword KwWhere),
           ("of"    , TokKeyword KwOf),
           ("end"   , TokKeyword KwEnd)]
