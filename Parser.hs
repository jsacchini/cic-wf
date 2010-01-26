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

tempParse = (runParser $ (runReaderT $ cxtParser parseExpr) []) () ""

-- tempParse' p = (runParser $ runCxtParser p) () ""

deriving instance Typeable ParseError
instance Exception ParseError

type ExprPos = (Expr, SourcePos)
type TypeDecl = (Name, ExprPos)

newtype CxtParserM m a = CxtParserM { cxtParser :: ReaderT [TypeDecl] m a }
                         deriving(Monad, MonadReader [TypeDecl], MonadTrans)

type CxtParser a = CxtParserM (GenParser Char ()) a


runrun :: GenParser tok () a -> [tok] -> IO a
runrun p s = case runParser p () "" s of
               Left e -> throwIO e
               Right t -> return t

runrunExpr = fmap fst . runrun pExpr

runCxtParser :: CxtParserM m a -> m a
runCxtParser = flip runReaderT [] . cxtParser

pExpr :: CharParser () ExprPos
pExpr = runCxtParser pExpr_

parseLet = do whiteSpace
	      symbol "let"
	      x <- identifier
	      symbol ":="
	      (t, _) <- pExpr_
	      return (x, t)
			 

parseExpr = do whiteSpace
               (t,_) <- pExpr_
               return t

pExpr_ :: CxtParser ExprPos
pExpr_ = pPi <||> 
        pLam <||> 
        do sPos <- lift getPosition
           e <- pExpr1 sPos
           local (("",e):) $ pRest sPos e

pExpr1 = pExpr1_

liftedMany :: CxtParser a -> CxtParser [a]
liftedMany p = do x <- p
                  xs <- liftedMany p
                  return (x:xs)
               <||> return []

pExpr1_ :: SourcePos -> CxtParser ExprPos
pExpr1_ sPos = do f <- pExpr2
                  args <- liftedMany pExpr2
                  let sEnd = snd $ last (f:args) in
                   return (foldl (\r (e,p) -> App (mkPos sPos p) r e) (fst f) args, sEnd)

pExpr2 = pExpr2_

pExpr2_ :: CxtParser ExprPos
pExpr2_ = pIdent <||> pSort <||> pparenExpr

pparenExpr :: CxtParser ExprPos
pparenExpr = do symbol "("
                e <- pExpr_
                symbol ")"
                return e

pRest :: SourcePos -> ExprPos -> CxtParser ExprPos
pRest sPos e = do symbol "->"
                  (e2, sEnd) <- pExpr_
                  return (Pi (mkPos sPos sEnd) "" (fst e) e2, sEnd)
               <||> return e

pPi :: CxtParser ExprPos
pPi = do sPos <- lift getPosition
         reserved "forall"
         pBinds (pBuildPi sPos "," Pi)

pBuildPi :: SourcePos -> String -> (Position -> Name -> Expr -> Expr -> Expr) -> CxtParser ExprPos
pBuildPi sPos s f = do symbol s
                       (u, sEnd) <- pExpr_
                       ((x1,(t1,_)):bs) <- ask
                       return (foldl (\r (x,(e,p)) -> f (mkPos p sEnd) x e r) u ((x1,(t1,sPos)):bs), sEnd)

pLam :: CxtParser ExprPos
pLam = do sPos <- lift getPosition
          reserved "fun"
          pBinds (pBuildPi sPos "=>" Lam)

liftedMany1 :: CxtParser a -> CxtParser [a]
liftedMany1 p = do x <- p
                   xs <- liftedMany p
                   return (x:xs)

pBinds :: CxtParser ExprPos -> CxtParser ExprPos
pBinds p = pBind p <||> pparenBind p

pBind :: CxtParser ExprPos -> CxtParser ExprPos
pBind p = do sPos <- lift getPosition
             x <- identifier
             symbol ":"
             (t,_) <- pExpr_
             local ((x,(t,sPos)):) p

pparenBind :: CxtParser ExprPos -> CxtParser ExprPos
pparenBind p = do sPos <- lift getPosition
                  symbol "("
                  pBind (symbol ")" >> pparenBind p)
               <||> p   


(<||>) :: CxtParser a -> CxtParser a -> CxtParser a
(<||>) m n = CxtParserM $ ReaderT $ \r -> runReaderT (cxtParser m) r <|> runReaderT (cxtParser n) r

pSort :: CxtParser ExprPos
pSort = foldl1 (<||>) $ map pReserved [("Type",Box), ("Prop",Star)]
        where pReserved (s,r) = do sPos <- lift getPosition
                                   symbol s
                                   let sEnd = updatePosString sPos s in
                                    return (TSort (mkPos sPos sEnd) r, sEnd)


pIdent :: CxtParser ExprPos
pIdent = do sPos <- lift getPosition
            x <- identifier
            st <- ask
            let sEnd = updatePosString sPos x in
             case elemIndex x (map fst st) of
               Just n -> return (Bound (mkPos sPos sEnd) n, sEnd)
               Nothing -> return (Free (mkPos sPos sEnd) x, sEnd)
{-----

expr ::= "forall" bind "," expr
       | "fun" bind "=>" expr
       | expr1 rest

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

-----}


lexer :: P.TokenParser ()
lexer  = P.makeTokenParser 
         (emptyDef
         { P.commentStart    = "(*",
           P.commentEnd      = "*)",
           P.commentLine     = "--",
           P.reservedNames   = ["forall", "fun", "Type", "Prop", "let"],
           P.reservedOpNames = ["->", "=>", ",", ":="],
           P.opLetter        = oneOf ",->:="
         })

parens :: Parser a -> CxtParser a
parens          = lift . P.parens lexer

whiteSpace :: CxtParser ()
whiteSpace      = lift $ P.whiteSpace lexer

symbol :: String -> CxtParser String
symbol          = lift . P.symbol lexer

identifier :: CxtParser String
identifier      = lift $ P.identifier lexer

reserved :: String -> CxtParser ()
reserved        = lift . P.reserved lexer
