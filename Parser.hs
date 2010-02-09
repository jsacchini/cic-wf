{-# LANGUAGE PackageImports, FlexibleContexts, GeneralizedNewtypeDeriving,
  StandaloneDeriving, DeriveDataTypeable
 #-}
module Parser where

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

newtype CxtParserM m a = CxtParserM { cxtParser :: ReaderT [Name] m a }
                         deriving(Monad, MonadReader [Name], MonadTrans,
                                  Functor)

type CxtParser a = CxtParserM (GenParser Char ()) a

runCxtParser :: CxtParserM m a -> m a
runCxtParser = flip runReaderT [] . cxtParser


(<||>) :: CxtParser a -> CxtParser a -> CxtParser a
(<||>) m n = CxtParserM $ ReaderT $ \r -> runReaderT (cxtParser m) r <|> runReaderT (cxtParser n) r

pVar :: CxtParser ExprPos
pVar = do sPos <- lift getPosition
          x <- liftIdentifier
          st <- ask
          let sEnd = updatePosString sPos x in
           case elemIndex x st of
             Just n -> return (Bound (mkPos sPos sEnd) n, sEnd)
             Nothing -> return (Free (mkPos sPos sEnd) x, sEnd)

pMeta :: CxtParser ExprPos
pMeta = do sPos <- lift getPosition
           liftSymbol "_"
           let sEnd = updatePosString sPos "_" in
            return (EVar (mkPos sPos sEnd) Nothing, sEnd)

pEVar :: CxtParser ExprPos
pEVar = do sPos <- lift getPosition
           lift $ char '?'
           ns <- lift $ many digit
           let sEnd = updatePosString sPos ('?':ns) in
            return (EVar (mkPos sPos sEnd) (Just $ read ns), sEnd)

pIdent :: CxtParser ExprPos
pIdent = pVar
pIdentMeta :: CxtParser ExprPos
pIdentMeta = pVar <||> pMeta <||> pEVar


parseFile :: CharParser () [Command]
parseFile = whiteSpace >> many (parseCommand pIdent)
               

parseCommand :: CxtParser ExprPos -> CharParser () Command
parseCommand p = whiteSpace >> (parseLet p <|> parseLoad p <|> parseAxiom p <|> parseRefine)

-- parseAxiom :: CxtParser ExprPos -> CharParser () (Command a)
parseAxiom p = do reserved "axiom"
                  x <- identifier
                  symbol ":"
                  t <- parseExpr p
                  symbol "."
                  return $ Axiom x t

parseLoad :: CxtParser ExprPos -> CharParser () Command
parseLoad p = do reserved "import"
                 symbol "\""
                 xs <- many $ alphaNum <|> oneOf "."
                 symbol "\""
                 symbol "."
                 return $ Load xs

parseLet :: CxtParser ExprPos -> CharParser () Command
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

-- pIdentMeta :: CharParser () String
-- pIdentMeta = do x <- identifier
--                 if x == "_"
--                  then fail $ messageString (UnExpect "_")
--                  else return x

pMaybeExpr :: CxtParser ExprPos -> CharParser () (Maybe Expr)
pMaybeExpr p = do reservedOp ":"
                  e <- parseExpr p
                  return $ Just e
               <|> return Nothing

parseExpr :: CxtParser ExprPos -> CharParser () Expr
parseExpr = fmap fst . runCxtParser . pExpr_

pExpr_ :: CxtParser ExprPos -> CxtParser ExprPos
pExpr_ p = pPi p <||> 
           pLam p <||> 
           do sPos <- lift getPosition
              e <- pExpr1 p sPos
              rest <- local ("":) $ pRest p
              case rest of
                Just (e1, ePos) -> return (Pi (mkPos sPos ePos) "" (fst e) e1, ePos)
                Nothing -> return e

liftedMany :: CxtParser a -> CxtParser [a]
liftedMany p = do x <- p
                  xs <- liftedMany p
                  return (x:xs)
               <||> return []

pExpr1 :: CxtParser ExprPos -> SourcePos -> CxtParser ExprPos
pExpr1 p sPos = do f <- pExpr2 p
                   args <- liftedMany (pExpr2 p)
                   let sEnd = snd $ last (f:args) in
                    return (foldl (\r (e,p) -> App (mkPos sPos p) r e) (fst f) args, sEnd)

-- pExpr2 :: Bool -> CxtParser ExprPos
pExpr2 p = p <||> pSort <||> pparenExpr p

pparenExpr :: CxtParser ExprPos -> CxtParser ExprPos
pparenExpr p = do sPos <- lift getPosition
                  liftSymbol "("
                  e <- pExpr_ p
                  (do liftSymbol ")"
                      return e
                   <||>
                   do liftSymbol "::"
                      (e2, _) <- pExpr_ p
                      ePos <- lift getPosition
                      liftSymbol ")"
                      return (Ann (mkPos sPos ePos) (fst e) e2, ePos))

pRest :: CxtParser ExprPos -> CxtParser (Maybe ExprPos)
pRest p = do liftReservedOp "->"
             fmap Just (pExpr_ p)
          <||> return Nothing

pPi :: CxtParser ExprPos -> CxtParser ExprPos
pPi p = do sPos <- lift getPosition
           liftReserved "forall"
           ((do (x, e) <- pparenBind p
                (e1, ePos) <- local (x:) $ pRestPi p
                return (Pi (mkPos sPos ePos) x (fst e) e1, ePos))
            <||>
            (do (x, e) <- pBind p
                liftReservedOp ","
                (e1, ePos) <- local (x:) $ pExpr_ p
                return (Pi (mkPos sPos ePos) x (fst e) e1, ePos)))


pRestPi :: CxtParser ExprPos -> CxtParser ExprPos
pRestPi p = do sPos <- lift getPosition
               (x, e) <- pparenBind p
               (e1, ePos) <- local (x:) $ pRestPi p
               return (Pi (mkPos sPos ePos) x (fst e) e1, ePos)
            <||>
            do liftReservedOp ","
               pExpr_ p

pLam :: CxtParser ExprPos -> CxtParser ExprPos
pLam p = do sPos <- lift getPosition
            liftReserved "fun"
            ((do (x, e) <- pparenBind p
                 (e1, ePos) <- local (x:) $ pRestLam p
                 return (Lam (mkPos sPos ePos) x (fst e) e1, ePos))
             <||>
             (do (x, e) <- pBind p
                 liftReservedOp "=>"
                 (e1, ePos) <- local (x:) $ pExpr_ p
                 return (Lam (mkPos sPos ePos) x (fst e) e1, ePos)))

pRestLam :: CxtParser ExprPos -> CxtParser ExprPos
pRestLam p = do sPos <- lift getPosition
                (x, e) <- pparenBind p
                (e1, ePos) <- local (x:) $ pRestLam p
                return (Lam (mkPos sPos ePos) x (fst e) e1, ePos)
             <||>
             do liftReservedOp "=>"
                pExpr_ p

liftedMany1 :: CxtParser a -> CxtParser [a]
liftedMany1 p = do x <- p
                   xs <- liftedMany p
                   return (x:xs)

pBind :: CxtParser ExprPos -> CxtParser (Name, ExprPos)
pBind p = do x <- liftIdentifier
             liftSymbol ":"
             e <- pExpr_ p
             return (x,e)

pparenBind :: CxtParser ExprPos -> CxtParser (Name, ExprPos)
pparenBind p = do liftSymbol "("
                  r <- pBind p
                  liftSymbol ")"
                  return r


pSort :: CxtParser ExprPos
pSort = foldl1 (<||>) $ map pReserved [("Type",Box), ("Prop",Star)]
        where pReserved (s,r) = do sPos <- lift getPosition
                                   liftReserved s
                                   let sEnd = updatePosString sPos s in
                                    return (TSort (mkPos sPos sEnd) r, sEnd)


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

liftSymbol          = lift . P.symbol lexer
liftIdentifier      = lift $ P.identifier lexer
liftReserved        = lift . P.reserved lexer
liftReservedOp      = lift . P.reservedOp lexer

whiteSpace      = P.whiteSpace lexer
symbol          = P.symbol lexer
identifier      = P.identifier lexer
reserved        = P.reserved lexer
reservedOp      = P.reservedOp lexer
