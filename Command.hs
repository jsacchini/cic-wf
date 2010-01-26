{-# LANGUAGE PackageImports #-}

module Command where

import "mtl" Control.Monad.State
import "mtl" Control.Monad.Error

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Prim
import qualified Text.ParserCombinators.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language(emptyDef)

import Environment
import Abstract
import qualified Parser as P
import qualified Internal as I
import TCM
import Typing


data Command = Definition Name (Maybe Expr) Expr
             | Axiom Name Expr
             | Check Expr
             | Load FilePath


inferCatch :: Result () -> Result ()
inferCatch p = p `catchError` \err -> liftIO $ putStrLn $ "Typing Error:\n" ++ show err

processCommand :: Command -> Result ()
processCommand (Definition x t u) = inferCatch $ processDef x t u

processDef :: Name -> Maybe Expr -> Expr -> Result ()
processDef x (Just t) u = do check u (I.interp t)
                             g <- get
                             put (extendEnv x (Def (I.interp u) (I.interp t)) g)
processDef x Nothing u = do r <- infer u
                            g <- get
                            put (extendEnv x (Def (I.interp u) r) g)


pExpr :: CharParser () Expr
pExpr = fmap fst $ P.pExpr
                    
pCommand :: CharParser () Command
pCommand = pDef

pDef :: CharParser () Command
pDef = do whiteSpace
          reserved "let"
          x <- identifier
          t <- pMaybeExpr
          symbol ":="
          e <- pExpr
          symbol "."
          return $ Definition x t e
          
pMaybeExpr = do reservedOp ":"
                e <- pExpr
                return $ Just e
             <|> return Nothing


lexer :: Tok.TokenParser ()
lexer  = Tok.makeTokenParser 
         (emptyDef
         { Tok.reservedNames   = ["let", "axiom", "load"],
           Tok.reservedOpNames = [":", ":=", "."],
           Tok.opStart         = oneOf ":.",
           Tok.opLetter        = oneOf "=."
         })

parens     = Tok.parens lexer
whiteSpace = Tok.whiteSpace lexer
reservedOp = Tok.reservedOp lexer
symbol     = Tok.symbol lexer
identifier = Tok.identifier lexer
reserved   = Tok.reserved lexer
