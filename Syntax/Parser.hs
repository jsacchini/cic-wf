{-# LANGUAGE PackageImports, FlexibleContexts, GeneralizedNewtypeDeriving,
  StandaloneDeriving, DeriveDataTypeable
 #-}
module Syntax.Parser
    (parseExpr, parseTopLevelCommand, parseFile,
     parseExprMeta,
     Syntax.Parser.runParser, ParsingError
    ) where

import Data.List
import Data.Typeable

import "mtl" Control.Monad.Reader
import Control.Exception

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Prim as Prim
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language(emptyDef)

import Syntax.Abstract
import Syntax.Bind
import Syntax.Position

type ExprPos = (Expr, SourcePos) -- final position

data ParsingError = ParsingError ParseError
                    deriving(Typeable,Show)

instance Exception ParsingError

runParser :: (MonadIO m) => FilePath -> CharParser () a -> String -> m a
runParser f p s = liftIO $ case Prim.runParser p () f s of
                             Left e -> throwIO $ ParsingError e
                             Right t -> return t


parseEOF p = do e <- p
                eof
                return e


parseFile :: CharParser () [Command]
parseFile = parseEOF $ whiteSpace >> many parseCommand
            where parseCommand = whiteSpace >> (parseLet <|> parseLoad <|> parseAxiom <|> parseInd)

parseTopLevelCommand :: CharParser () Command
parseTopLevelCommand = parseEOF $ whiteSpace >>
                       (parseLet <|> parseLoad <|> parseAxiom <|> parseInd)

parseAxiom :: CharParser () Command
parseAxiom = do reserved "axiom"
                x <- identifier
                reservedOp ":"
                t <- fmap fst (pExpr pVar)
                reservedOp "."
                return $ AxiomCommand x t

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
              reservedOp ":="
              e <- fmap fst (pExpr pVar)
              reservedOp "."
              return $ Definition x t e

-- parseRefine :: CharParser () Command
-- parseRefine = do reserved "refine"
--                  x <- identifier
--                  symbol ":"
--                  t <- fmap fst pExpr
--                  symbol ":="
--                  e <- fmap fst pExpr
--                  symbol "."
--                  return $ Refine x t e

parseInd :: CharParser () Command
parseInd = do reserved "data"
              i <- identifier
              bs <- many $ parens pBind
              reservedOp ":"
              arg <- fmap fst (pExpr pVar)
              reservedOp ":="
              cs <- many parseConstr
              symbol "."
              return $ Inductive (MkInd i bs arg cs)

parseConstr = do reservedOp "|"
                 n <- identifier
                 reservedOp ":"
                 e <- fmap fst (pExpr pVar)
                 return $ MkConstrExpr n e

pBind :: CharParser () BindE
pBind = do x <- identifier
           symbol ":"
           e <- fmap fst (pExpr pVar)
           return $ Bind x e

parseExpr :: GenParser Char () Expr
parseExpr = parseEOF $ whiteSpace >> fmap fst (pExpr pVar)

parseExprMeta :: GenParser Char () Expr
parseExprMeta = parseEOF $ whiteSpace >> fmap fst (pExpr pIdent)

pMaybeExpr :: CharParser () (Maybe Expr)
pMaybeExpr = do reservedOp ":"
                e <- fmap fst (pExpr pVar)
                return $ Just e
             <|> return Nothing

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
pIdent = pVar <|> pMeta <|> pEVar


pExpr :: CharParser () ExprPos -> CharParser () ExprPos
pExpr p = pExpr0
    where
      pExpr0 = parsePos $ do e <- pExpr_
                             (do reservedOp "::"
                                 (e2, ePos) <- pExpr_
                                 return (Ann noPos (fst e) e2, ePos)
                              <|> return e)

      pExpr_ :: CharParser () ExprPos
      pExpr_ = pPi <|>
               pLam <|>
               pMatch <|>
               pFix <|>
               do sPos <- getPosition
                  e <- pExpr1 sPos
                  rest <- pRest
                  case rest of
                    Just (e1, ePos) -> return (Pi (mkPos sPos ePos) (NoBind $ fst e) e1, ePos)
                    Nothing -> return e


      pExpr1 :: SourcePos -> CharParser () ExprPos
      pExpr1 sPos = do f <- pExpr2
                       args <- many $ pExpr2
                       let ePos = snd $ last (f:args) in
                        return (foldl (\r (e,p) -> App (mkPos sPos p) r e) (fst f) args, ePos)

      pExpr2 :: CharParser () ExprPos
      pExpr2 = p <|> pSort <|> parens pExpr0

      pRest :: CharParser () (Maybe ExprPos)
      pRest = do reservedOp "->"
                 fmap Just pExpr0
              <|> return Nothing

      pFix :: CharParser () ExprPos
      pFix = parsePos $ do reserved "fix"
                           ns <- fmap read (many digit)
                           whiteSpace
                           f <- identifier
                           bs <- many $ parens pBind
                           reservedOp ":"
                           ret <- fmap fst pExpr0
                           reservedOp ":="
                           (e, ePos) <- pExpr0
                           return (Fix noPos ns f bs ret e, ePos)

      pMatch :: CharParser () ExprPos
      pMatch = parsePos $ do reserved "match"
                             e <- fmap fst pExpr0
                             aname <- optionMaybe pAsName
                             iname <- optionMaybe pInName
                             ret <- optionMaybe pReturn
                             reserved "with"
                             bs <- many pBranch
                             ePos <- fmap (flip updatePosString "end") getPosition
                             reserved "end"
                             return $ (Match noPos (MkMatch e aname iname ret bs), ePos)

      pAsName = reserved "as" >> identifier
      pInName = reserved "in" >> fmap (\xs -> (head xs, tail xs)) (many1 identifier)
      pReturn = reserved "return" >> fmap fst pExpr0

      pBranch :: CharParser () Branch
      pBranch = do reservedOp "|"
                   c <- identifier
                   as <- many identifier
                   symbol "=>"
                   e <- fmap fst pExpr0
                   return $ MkBranch c 0 as e -- in scope we put the right number

      pPi :: CharParser () ExprPos
      pPi = parsePos $ do reserved "forall"
                          bs <- pBinds
                          reservedOp ","
                          (e, ePos) <- pExpr0
                          return $ (foldr (\(sp, b) r -> Pi (mkPos sp ePos) b r) e bs, ePos)

      pLam :: CharParser () ExprPos
      pLam = parsePos $ do reserved "fun"
                           bs <- pBinds
                           reservedOp "=>"
                           (e, ePos) <- pExpr0
                           return $ (foldr (\(sp, b) r -> Lam (mkPos sp ePos) b r) e bs, ePos)

      pBinds :: CharParser () [(SourcePos, BindE)]
      pBinds = do sPos <- getPosition
                  b <- pBind
                  return [(sPos, b)]
               <|> (many1 $ do sPos <- getPosition
                               b <- parens pBind
                               return (sPos, b))

      -- pFix p = do sPos <- getPosition
      --             reserved "fix"
      --             n <- many digit
      --             f <- identifier
      --             symbol ":"
      --             t <- fmap fst $ pExpr p
      --             symbol ":="
      --             (e, ePos) <- pExpr p
      --             return $ Fix n f

      pSort :: CharParser () ExprPos
      pSort = foldl1 (<|>) $ map pReserved [("Type",Box), ("Prop",Star)]
              where pReserved (s,r) = do sPos <- getPosition
                                         reserved s
                                         let ePos = updatePosString sPos s in
                                          return (TSort (mkPos sPos ePos) r, ePos)

      parsePos :: CharParser () ExprPos -> CharParser () ExprPos
      parsePos p = do sPos <- getPosition
                      (e, ePos) <- p
                      return (updatePos (mkPos sPos ePos) e, ePos)

updatePos :: Position -> Expr -> Expr
updatePos p (Ann _ e1 e2) = Ann p e1 e2
updatePos p (TSort _ s) = TSort p s
updatePos p (Pi _ e1 e2) = Pi p e1 e2
updatePos p (Var _ x) = Var p x
updatePos p (Bound _ n) = Bound p n
updatePos p (EVar _ n) = EVar p n
updatePos p (Lam _ e1 e2) = Lam p e1 e2
updatePos p (App _ e1 e2) = App p e1 e2
updatePos p (Match _ e) = Match p e
updatePos p (Fix _ n f rs r e) = Fix p n f rs r e


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
                                "import", "axiom", "refine", "match", "as", "in",
                                "return", "with", "end", "data", "fix"],
           P.reservedOpNames = ["->", "=>", ",", ":=", ":", ".", "::"],
           P.identStart      = letter,
           P.identLetter     = alphaNum,
           P.opStart         = oneOf ",-=:.",
           P.opLetter        = oneOf ",>:=."
         })

whiteSpace      = P.whiteSpace lexer
parens          = P.parens lexer
symbol          = P.symbol lexer
identifier      = P.identifier lexer
reserved        = P.reserved lexer
reservedOp      = P.reservedOp lexer
