module Syntax

extend lang::std::Layout;
extend lang::std::Id;

/*
 * Concrete syntax of QL
 */

start syntax Form 
  = "form" Id "{" Question* "}"; 

// TODO: question, computed question, block, if-then-else, if-then
syntax Question
  = Str string Id identifier ":" Type type
  | Str string Id identifier ":" Type type "=" Expr expr //computed question
  | "if ("Expr expression") {" Block "}"
  ; 

syntax Block
  = Question*
  | Question* "} else {" Block "}"
  ;

// TODO: +, -, *, /, &&, ||, !, >, <, <=, >=, ==, !=, literals (bool, int, str)
// Think about disambiguation using priorities and associativity
// and use C/Java style precedence rules (look it up on the internet)
syntax Expr 
  = Term 
  | AddExpr 
  | AndExpr
  | "!"Expr
  ;

syntax AndExpr
  = OrExpr 
  | AndExpr "&&" OrExpr
  ;
  
syntax OrExpr
  = ComExpr
  | OrExpr "||" AndExpr
  ;
  
syntax ComExpr
  = Primary "\>" Primary
  | | "||" Term Expr1
  | "\>" Term Expr1
  | "\<" Term Expr1
  | "\<=" Term Expr1
  | "\>=" Term Expr1
  | "==" Term Expr1
  | "!=" Term Expr1

  
syntax AddExpr
  = MulExpr
  | AddExpr "+" MulExpr
  | AddExpr "-" MulExpr
 ;

syntax MulExpr
  = Expr
  | Expr "*" MulExpr
  | Expr "/" MulExpr
  ;
  
syntax Primary
  = Bool
  | Int
  | Str
  | Id \ "true" \ "false" // true/false are reserved keywords.
  ;
/*
syntax Term
  = Expr Term1
  ;
   
syntax Expr1
  = "+" Term Expr1 
  | "-" Term Expr1
  | "||" Term Expr1
  | "\>" Term Expr1
  | "\<" Term Expr1
  | "\<=" Term Expr1
  | "\>=" Term Expr1
  | "==" Term Expr1
  | "!=" Term Expr1
  | ""
  ;

syntax Term1
  = "*" Expr Term1
  | "/" Expr Term1
  | "&&" Expr Term1
  | ""
  ;
*/ 
syntax Type
  = "boolean" | "integer";  
  
lexical Str = "\""![\n\"]*"\"";

lexical Int 
  = [0-9]+;

lexical Bool = "true" | "false";



