{-# LANGUAGE PackageImports, FlexibleContexts, GeneralizedNewtypeDeriving,
  StandaloneDeriving, DeriveDataTypeable
 #-}
module Syntax.Parser where

import Data.List

import "mtl" Control.Monad.Reader

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Prim
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language(emptyDef)

import Syntax.Abstract
import Syntax.Position

type ExprPos = (Expr, SourcePos) -- final position

parseEOF p = do e <- p
                eof
                return e


pVar :: CharParser () ExprPos
pVar = do sPos <- getPosition
          x <- identifier
          let ePos = updatePosString sPos x
          return (Var (mkPos sPos ePos) x, ePos)

pMeta :: CharParser () ExprPos
pMeta = do sPos <- getPosition
           symbol "_"
           let ePos = updatePosString sPos "_" in
            return (EVar (mkPos sPos ePos) Nothing, ePos)

pEVar :: CharParser () ExprPos
pEVar = do sPos <- getPosition
           char '?'
           ns <- many digit
           let ePos = updatePosString sPos ('?':ns) in
            return (EVar (mkPos sPos ePos) (Just $ read ns), ePos)

pIdent :: CharParser () ExprPos
pIdent = pVar
pIdentMeta :: CharParser () ExprPos
pIdentMeta = pVar <|> pMeta <|> pEVar


parseFile :: CharParser () [Command]
parseFile = parseEOF $ whiteSpace >> many parseCommand
            where parseCommand = whiteSpace >> (parseLet pIdent <|> parseLoad pIdent <|> parseAxiom pIdent)
               
parseTopLevelCommand :: CharParser () Command
parseTopLevelCommand = parseEOF $ (parseLet pIdentMeta <|> parseLoad pIdentMeta <|> parseAxiom pIdentMeta <|> parseRefine)

parseExpression = parseEOF $ whiteSpace >> parseExpr pIdent
parseExprMeta = parseEOF $ whiteSpace >> parseExpr pIdentMeta

parseAxiom :: CharParser () ExprPos -> CharParser () Command
parseAxiom p = do reserved "axiom"
                  x <- identifier
                  symbol ":"
                  t <- parseExpr p
                  symbol "."
                  return $ Axiom x t

parseLoad :: CharParser () ExprPos -> CharParser () Command
parseLoad p = do reserved "import"
                 symbol "\""
                 xs <- many $ alphaNum <|> oneOf "."
                 symbol "\""
                 symbol "."
                 return $ Load xs

parseLet :: CharParser () ExprPos -> CharParser () Command
parseLet p = do reserved "let"
                x <- identifier
                t <- pMaybeExpr p
                symbol ":="
                e <- parseExpr p
                symbol "."
                return $ Definition x t e

parseRefine :: CharParser () Command
parseRefine = do reserved "refine"
                 x <- identifier
                 symbol ":"
                 t <- parseExpr pIdentMeta
                 symbol ":="
                 e <- parseExpr pIdentMeta
                 symbol "."
                 return $ Refine x t e

pMaybeExpr :: CharParser () ExprPos -> CharParser () (Maybe Expr)
pMaybeExpr p = do reservedOp ":"
                  e <- parseExpr p
                  return $ Just e
               <|> return Nothing

parseExpr :: CharParser () ExprPos -> CharParser () Expr
parseExpr = fmap fst . pExpr_

pExpr_ :: CharParser () ExprPos -> CharParser () ExprPos
pExpr_ p = pPi p <|> 
           pLam p <|> 
           do sPos <- getPosition
              e <- pExpr1 p sPos
              rest <- pRest p
              case rest of
                Just (e1, ePos) -> return (Pi (mkPos sPos ePos) "" (fst e) e1, ePos)
                Nothing -> return e


pExpr1 :: CharParser () ExprPos -> SourcePos -> CharParser () ExprPos
pExpr1 p sPos = do f <- pExpr2 p
                   args <- many $ pExpr2 p
                   let ePos = snd $ last (f:args) in
                    return (foldl (\r (e,p) -> App (mkPos sPos p) r e) (fst f) args, ePos)

pExpr2 :: CharParser () ExprPos -> CharParser () ExprPos
pExpr2 p = p <|> pSort <|> pparenExpr p

pparenExpr :: CharParser () ExprPos -> CharParser () ExprPos
pparenExpr p = do sPos <- getPosition
                  symbol "("
                  e <- pExpr_ p
                  (do symbol ")"
                      return e
                   <|>
                   do symbol "::"
                      (e2, _) <- pExpr_ p
                      ePos <- getPosition
                      symbol ")"
                      return (Ann (mkPos sPos ePos) (fst e) e2, ePos))

pRest :: CharParser () ExprPos -> CharParser () (Maybe ExprPos)
pRest p = do reservedOp "->"
             fmap Just (pExpr_ p)
          <|> return Nothing

pPi :: CharParser () ExprPos -> CharParser () ExprPos
pPi p = do sPos <- getPosition
           reserved "forall"
           ((do (x, e) <- parens $ pBind p
                (e1, ePos) <- pRestPi p
                return (Pi (mkPos sPos ePos) x (fst e) e1, ePos))
            <|>
            (do (x, e) <- pBind p
                reservedOp ","
                (e1, ePos) <- pExpr_ p
                return (Pi (mkPos sPos ePos) x (fst e) e1, ePos)))


pRestPi :: CharParser () ExprPos -> CharParser () ExprPos
pRestPi p = do sPos <- getPosition
               (x, e) <- parens $ pBind p
               (e1, ePos) <- pRestPi p
               return (Pi (mkPos sPos ePos) x (fst e) e1, ePos)
            <|>
            do reservedOp ","
               pExpr_ p

pLam :: CharParser () ExprPos -> CharParser () ExprPos
pLam p = do sPos <- getPosition
            reserved "fun"
            ((do (x, e) <- parens $ pBind p
                 (e1, ePos) <- pRestLam p
                 return (Lam (mkPos sPos ePos) x (fst e) e1, ePos))
             <|>
             (do (x, e) <- pBind p
                 reservedOp "=>"
                 (e1, ePos) <- pExpr_ p
                 return (Lam (mkPos sPos ePos) x (fst e) e1, ePos)))

pRestLam :: CharParser () ExprPos -> CharParser () ExprPos
pRestLam p = do sPos <- getPosition
                (x, e) <- parens $ pBind p
                (e1, ePos) <- pRestLam p
                return (Lam (mkPos sPos ePos) x (fst e) e1, ePos)
             <|>
             do reservedOp "=>"
                pExpr_ p

pBind :: CharParser () ExprPos -> CharParser () (Name, ExprPos)
pBind p = do x <- identifier
             symbol ":"
             e <- pExpr_ p
             return (x,e)

pSort :: CharParser () ExprPos
pSort = foldl1 (<|>) $ map pReserved [("Type",Box), ("Prop",Star)]
        where pReserved (s,r) = do sPos <- getPosition
                                   reserved s
                                   let ePos = updatePosString sPos s in
                                    return (TSort (mkPos sPos ePos) r, ePos)


{-----

decl ::= "import" filename "."
       | "let" ident [: expr] ":=" expr "."

expr ::= "forall" bind "," expr
       | "fun" bind "=>" expr
       | "match" expr "as" ident in ... "return" expr "with" branch* "end"
       | "fix" ident ":" expr ":=" expr
       | expr1 rest

branch ::= "|" ident+ "=>" expr

rest ::= "->" expr
       | empty

expr1 ::= expr2
        | expr2 expr2*

expr2 ::= "(" expr ")"
        | sort
        | id

bind ::= var ":" expr
       | parenbind+

parenbind ::= "(" var ":" expr ")"

dec ::= "Definition" var parenbind1 ":" expr ":=" expr "."
      | "Check" expr "."

ind ::= "data" ident bind ":" indsort ":=" constr

constr ::= "|" ident ":" constrtype

constrtype ::= "forall" bind "," constrtype1
             | constrtype1

constrtype1 ::= ident expr*
              | expr -> constrtype1
             
types for inductive types

indsort ::= "forall" bind "," indsort1
          | indsort1

indsort1 ::= sort
           | expr -> indsort1

-----}


lexer :: P.TokenParser ()
lexer  = P.makeTokenParser 
         (emptyDef
         { P.commentStart    = "(*",
           P.commentEnd      = "*)",
           P.commentLine     = "--",
           P.reservedNames   = ["forall", "fun", "Type", "Prop", "let",
                                "import", "axiom", "refine"],
           P.reservedOpNames = ["->", "=>", ",", ":=", ":", "."],
           P.identStart      = letter,
           P.identLetter     = alphaNum,
           P.opLetter        = oneOf ",->:=."
         })

whiteSpace      = P.whiteSpace lexer
parens          = P.parens lexer
symbol          = P.symbol lexer
identifier      = P.identifier lexer
reserved        = P.reserved lexer
reservedOp      = P.reservedOp lexer
