{-# LANGUAGE PackageImports, FlexibleContexts, GeneralizedNewtypeDeriving,
  StandaloneDeriving, DeriveDataTypeable
 #-}
module Parser where

import Control.Exception
import "mtl" Control.Monad.Error
import Data.Typeable
import Data.List
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Prim
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language(emptyDef)
import "mtl" Control.Monad.Reader

import Abstract
import Position

deriving instance Typeable ParseError
instance Exception ParseError

type ExprPos = (Expr, SourcePos)
type TypeDecl = (Name, ExprPos)

newtype CxtParserM m a = CxtParserM { cxtParser :: ReaderT [TypeDecl] m a }
                         deriving(Monad, MonadReader [TypeDecl], MonadTrans,
                                 Functor)

type CxtParser a = CxtParserM (GenParser Char ()) a

runCxtParser :: CxtParserM m a -> m a
runCxtParser = flip runReaderT [] . cxtParser

runParserIO :: FilePath -> GenParser tok () a -> [tok] -> IO a
runParserIO f p s = case runParser p () f s of
                      Left e -> throwIO e
                      Right t -> return t

parseEOF p = do e <- p
                eof
                return e

parseFile :: CharParser () [Command]
parseFile = whiteSpace >> many parseCommand
               

parseCommand :: CharParser () Command
parseCommand = whiteSpace >> (parseLet <|> parseLoad <|> parseAxiom)

parseAxiom = do reserved "axiom"
                x <- identifier
                symbol ":"
                t <- parseExpr
                symbol "."
                return $ Axiom x t

parseLoad :: CharParser () Command
parseLoad = do reserved "import"
               symbol "\""
               xs <- many $ alphaNum <|> oneOf "."
               symbol "\""
               symbol "."
               return $ Load xs

parseLet :: CharParser () Command
parseLet = do reserved "let"
              x <- identifier
              t <- pMaybeExpr
              symbol ":="
              e <- parseExpr
              symbol "."
              return $ Definition x t e

pMaybeExpr :: CharParser () (Maybe Expr)
pMaybeExpr = do reservedOp ":"
                e <- parseExpr
                return $ Just e
             <|> return Nothing

parseExpr :: CharParser () Expr
parseExpr = fmap fst $ runCxtParser pExpr_

pExpr_ :: CxtParser ExprPos
pExpr_ = pPi <||> 
        pLam <||> 
        do sPos <- lift getPosition
           e <- pExpr1 sPos
           local (("",e):) $ pRest sPos e

liftedMany :: CxtParser a -> CxtParser [a]
liftedMany p = do x <- p
                  xs <- liftedMany p
                  return (x:xs)
               <||> return []

pExpr1 :: SourcePos -> CxtParser ExprPos
pExpr1 sPos = do f <- pExpr2
                 args <- liftedMany pExpr2
                 let sEnd = snd $ last (f:args) in
                  return (foldl (\r (e,p) -> App (mkPos sPos p) r e) (fst f) args, sEnd)

pExpr2 :: CxtParser ExprPos
pExpr2 = pIdent <||> pSort <||> pparenExpr

pparenExpr :: CxtParser ExprPos
pparenExpr = do liftSymbol "("
                e <- pExpr_
                liftSymbol ")"
                return e

pRest :: SourcePos -> ExprPos -> CxtParser ExprPos
pRest sPos e = do liftReservedOp "->"
                  (e2, sEnd) <- pExpr_
                  return (Pi (mkPos sPos sEnd) "" (fst e) e2, sEnd)
               <||> return e

pPi :: CxtParser ExprPos
pPi = do sPos <- lift getPosition
         liftReserved "forall"
         pBinds (pBuildPi sPos "," Pi)

pBuildPi :: SourcePos -> String -> (Position -> Name -> Expr -> Expr -> Expr) -> CxtParser ExprPos
pBuildPi sPos s f = do liftReservedOp s
                       (u, sEnd) <- pExpr_
                       ((x1,(t1,_)):bs) <- ask
                       return (foldl (\r (x,(e,p)) -> f (mkPos p sEnd) x e r) u ((x1,(t1,sPos)):bs), sEnd)

pLam :: CxtParser ExprPos
pLam = do sPos <- lift getPosition
          liftReserved "fun"
          pBinds (pBuildPi sPos "=>" Lam)

liftedMany1 :: CxtParser a -> CxtParser [a]
liftedMany1 p = do x <- p
                   xs <- liftedMany p
                   return (x:xs)

pBinds :: CxtParser ExprPos -> CxtParser ExprPos
pBinds p = pBind p <||> pparenBind p

pBind :: CxtParser ExprPos -> CxtParser ExprPos
pBind p = do sPos <- lift getPosition
             x <- liftIdentifier
             liftSymbol ":"
             (t,_) <- pExpr_
             local ((x,(t,sPos)):) p

pparenBind :: CxtParser ExprPos -> CxtParser ExprPos
pparenBind p = do sPos <- lift getPosition
                  liftSymbol "("
                  pBind (liftSymbol ")" >> pparenBind p)
               <||> p   


(<||>) :: CxtParser a -> CxtParser a -> CxtParser a
(<||>) m n = CxtParserM $ ReaderT $ \r -> runReaderT (cxtParser m) r <|> runReaderT (cxtParser n) r

pSort :: CxtParser ExprPos
pSort = foldl1 (<||>) $ map pReserved [("Type",Box), ("Prop",Star)]
        where pReserved (s,r) = do sPos <- lift getPosition
                                   liftSymbol s
                                   let sEnd = updatePosString sPos s in
                                    return (TSort (mkPos sPos sEnd) r, sEnd)


pIdent :: CxtParser ExprPos
pIdent = do sPos <- lift getPosition
            x <- liftIdentifier
            st <- ask
            let sEnd = updatePosString sPos x in
             case elemIndex x (map fst st) of
               Just n -> return (Bound (mkPos sPos sEnd) n, sEnd)
               Nothing -> return (Free (mkPos sPos sEnd) x, sEnd)
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
           P.reservedNames   = ["forall", "fun", "Type", "Prop", "let", "import"],
           P.reservedOpNames = ["->", "=>", ",", ":=", ":", "."],
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
