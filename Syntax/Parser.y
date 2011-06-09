{

-- | Generated by Happy (<http://www.haskell.org/happy>)
--
-- TODO
--
-- * Check if BindName is used in all places where a _ can be used instead
--   of an actual name.


module Syntax.Parser(exprParser,
                     fileParser) where

import Control.Monad.State

import Syntax.Tokens
import Syntax.Lexer
import Syntax.ParseMonad
import Syntax.Position
import Syntax.Size
import Syntax.Common
import Syntax.Alex
import qualified Syntax.Abstract as A

import Utils.Misc

}


%name exprParser Exp
%name fileParser Decls
%tokentype { Token }
%monad { Parser }
%lexer { lexer } { TokEOF }

%right '->'

%token
  'forall'         { TokKeyword KwForall $$ }
  'fun'            { TokKeyword KwFun $$ }
  'prop'           { TokKeyword KwProp $$ }
  'assume'         { TokKeyword KwAssume $$ }
  'define'         { TokKeyword KwDefine $$ }
  'eval'           { TokKeyword KwEval $$ }
  'data'           { TokKeyword KwData $$ }
  'case'           { TokKeyword KwCase $$ }
  'in'             { TokKeyword KwIn $$ }
  'of'             { TokKeyword KwOf $$ }
  'fix'            { TokKeyword KwFix $$ }
  'where'          { TokKeyword KwWhere $$ }
  'end'            { TokKeyword KwEnd $$ }


  '('              { TokSymbol SymbLeftParen $$}
  ')'              { TokSymbol SymbRightParen $$}
  '.'              { TokSymbol SymbDot $$ }
  ':='             { TokSymbol SymbColonEq $$ }
  ':'              { TokSymbol SymbColon $$ }
  ','              { TokSymbol SymbComma $$ }
  '=>'             { TokSymbol SymbImplies $$ }
  '->'             { TokSymbol SymbArrow $$ }
  '|'              { TokSymbol SymbBar $$ }
  '+'              { TokSymbol SymbPos $$ }
  '-'              { TokSymbol SymbNeg $$ }
  '++'             { TokSymbol SymbSPos $$ }
  '@'              { TokSymbol SymbNeut $$ }
  '<'              { TokSymbol SymbLAngle $$ }
  '>'              { TokSymbol SymbRAngle $$ }
  '['              { TokSymbol SymbLBracket $$ }
  ']'              { TokSymbol SymbRBracket $$ }
  typeN            { TokType $$ }
  ident            { TokIdent $$ }
  identStar        { TokIdentStar $$ }

  number           { TokNumber $$ }

%%

Decls :: { [A.Declaration] }
Decls : DeclsR        { reverse $1 }

DeclsR :: { [A.Declaration] }
DeclsR : Decl '.'          { [$1] }
       | DeclsR Decl '.'   { $2 : $1 }

Decl :: { A.Declaration }
Decl
  : 'define' Name MaybeExp ':=' Exp
         { A.Definition (fuseRange $1 $5) (snd $2) $3 $5 }
  | 'assume' Name ':' Exp
         { A.Assumption (fuseRange $1 $4) (snd $2) $4 }
  | 'data' Name Parameters ':' Exp ':=' Constructors
         { A.Inductive (fuseRange $1 $7) (A.InductiveDef (snd $2) (reverse $3) $5 $7) }
  | 'eval' Exp
         { A.Eval (getRange $2) $2 }

Parameters :: { [A.Parameter] }
Parameters : Parameters Par            { $2 : $1 }
           | {- empty -}               { [] }

Par :: { A.Parameter }
Par : '(' NamesPol ':' Exp ')' { A.Parameter (fuseRange $1 $5) (reverse $2) $4 }

NamesPol :: { [(Name, Polarity)] }
NamesPol : NamesPol BindName Polarity    { (snd $2,$3) : $1 }
         | BindName Polarity             { [(snd $1,$2)] }

Polarity :: { Polarity }
Polarity : '+'            { Pos }
         | '-'            { Neg }
         | '++'           { SPos }
         | '@'            { Neut }
         | {- empty -}    { Neut } -- default polarity

-- For the first constructor, the '|' before its definition is optional
Constructors :: { [A.Constructor] }
Constructors : Constr1 Constr2       { maybe [] return $1 ++ reverse $2 }

Constr1 :: { Maybe A.Constructor }
Constr1 : BasicConstr            { Just $1 }
        | {- empty -}            { Nothing }

Constr2 :: { [A.Constructor] }
Constr2 : {- empty -}                { [] }
        | Constr2 '|' BasicConstr    { $3 : $1 }

-- Constructors are given id 0 by the parser. The actual id is given by the
-- scope checker.
BasicConstr :: { A.Constructor }
BasicConstr : Name ':' Exp      { let (p,x) = $1
                                   in A.Constructor (fuseRange p $3) x $3 0 }

Exp :: { A.Expr }
Exp : 'forall' Binding ',' Exp   { A.Pi (fuseRange $1 $4) $2 $4 }
    | 'fun' Binding '=>' Exp     { A.Lam (fuseRange $1 $4) $2 $4 }
    | Exps1 Rest                 { let r = mkApp $1
                                   in case $2 of
                                        Just e -> A.Arrow (fuseRange r e) r e
                                        Nothing -> r }
    -- | Exp '->' Exp               { A.Arrow (fuseRange $1 $3) $1 $3 }
    -- | Exps1                      { mkApp $1 }
    | Case                       { A.Case $1 }
    | Fix                        { A.Fix $1 }

-- Exps :: { [A.Expr] }
-- Exps : Exps Exp          { $2 : $1 }
--      | {- empty -}       { [] }

Exps1 :: { [A.Expr] }
Exps1 : Exp1           { [$1] }
      | Exps1 Exp1     { $2 : $1 }

Exp1 :: { A.Expr }
Exp1 : '(' Exp ')'   { $2 }
     | Sort          { $1 }
     | Name          { A.Ident (mkRangeLen (fst $1) (length (unName (snd $1)))) (snd $1) }
     | identStar     {% unlessM starAllowed (fail $ "position type not allowed" ++ show (fst $1)) >> return (A.Ind (mkRangeLen (fst $1) (length (snd $1))) Star (Id (snd $1))) }


-- This does not look elegant
Sort :: { A.Expr }
Sort : 'prop'  { A.Sort (mkRangeLen $1 4) Prop }
     | typeN   { let (pos, lvl) = $1
                 in  A.Sort (mkRangeLen pos (4 + length (show lvl))) (Type lvl) }


MaybeExp :: { Maybe A.Expr }
MaybeExp : ':' Exp       { Just $2 }
         | {- empty -}   { Nothing }

Rest :: { Maybe A.Expr }
Rest : '->' Exp          { Just $2 }
     | {- empty -}       { Nothing }

Case :: { A.CaseExpr }
Case : CaseRet 'case' CaseArg In WhereSubst 'of' Branches 'end'
                         { let rg = maybe (fuseRange $2 $8)
                                          (flip fuseRange $8) $1
                           in A.CaseExpr rg (fst $3) (snd $3) $4 $5 $1 $7 }

CaseArg :: { (A.Expr, Maybe Name) }
CaseArg : Name ':=' Exp      { ($3, Just (snd $1)) }
        | Exp                 { ($1, Nothing) }

CaseRet :: { Maybe A.Expr }
CaseRet : '<' Exp '>'     { Just $2 }
        | {- empty -}     { Nothing }

In :: { Maybe A.CaseIn }
In : 'in' InContext Name InArgs
                 { let r4 = reverse $4
                   in Just $ A.CaseIn (fuseRange $1 r4) $2 (snd $3) r4 }
   | {- empty -}
                 { Nothing }

InArgs :: { [A.Expr] }
InArgs : InArgs Exp1               { $2 : $1 }
       | {- empty -}               { [] }

InContext :: { [A.Bind] }
InContext : '[' Bindings ']'       { $2 }
          | {- empty -}            { [] }

Branches :: { [A.Branch] }
Branches : Branch1 Branch2   { maybe [] return $1 ++ reverse $2 }

Branch1 :: { Maybe A.Branch }
Branch1 : BasicBranch            { Just $1 }
        | {- empty -}            { Nothing }

Branch2 :: { [A.Branch] }
Branch2 : {- empty -}                { [] }
        | Branch2 '|' BasicBranch    { $3 : $1 }

BasicBranch :: { A.Branch }
BasicBranch : Name Pattern '=>' Exp WhereSubst
                             { let rg = maybe (fuseRange (fst $1) $4)
                                              (fuseRange (fst $1)) $5
                               in A.Branch rg (snd $1) 0 (reverse $2) $4 }

WhereSubst :: { Maybe A.Subst }
WhereSubst : 'where' Assigns     { Just (A.Subst $2) }
           | {- empty -}         { Nothing }


Assigns :: { [A.Assign] }
Assigns : Assigns '(' Name ':=' Exp ')'
                           { A.Assign (fuseRange $2 $6) (snd $3) $5 : $1 }
      | {- empty -}        { [] }

Fix :: { A.FixExpr }
Fix : 'fix' number Name ':' startPosType Exp endPosType ':=' Exp
                      { A.FixExpr (fuseRange $1 $9) (snd $2) (snd $3) $6 $9 }

startPosType :: { () }
startPosType : {- empty -}       {% allowStar }

endPosType :: { () }
endPosType : {- empty -}         {% forbidStar }

Bindings :: { [A.Bind] }
Bindings : Bindings '(' BasicBind ')'    { $3 : $1 }
         | {- empty -}                   { [] }

Binding :: { [A.Bind] }
Binding : BasicBind       { [$1] }
        | Bindings1       { reverse $1 }

Bindings1 :: { [A.Bind] }
Bindings1 : '(' BasicBind ')'             { [$2] }
          | Bindings1 '(' BasicBind ')'   { $3 : $1 }

BasicBind :: { A.Bind }
BasicBind : Names ':' Exp   { A.Bind (fuseRange (snd $1) $3) (fst $1) $3 }


Name :: { (Position, Name) }
Name : ident                { (fst $1, Id (snd $1)) }

Pattern :: { [Name] }
Pattern : Pattern Name       { snd $2 : $1 }
        | {- empty -}        { [] }

Names :: { ([Name], Range) }
Names : Names1              { let r = reverse $1
                              in (map snd r, fuseRanges $ map fst r) }

Names1 :: { [(Position, Name)] }
Names1 : BindName           { [$1] }
       | Names1 BindName    { $2 : $1 }

BindName :: { (Position, Name) }
BindName : ident            { let (p, x) = $1
                              in if x == "_" then (p, Id "") else (p, Id x) }

{

-- Required by Happy.
happyError :: Parser a
happyError = do s <- getLexerInput
                parseErrorAt (lexPos s) "Parser error"

-- Note that mkApp receives arguments in reverse order
mkApp :: [A.Expr] -> A.Expr
mkApp [x] = x
mkApp (x:y:ys) = A.App (fuseRange r x) r x
                 where r = mkApp (y:ys)


}
