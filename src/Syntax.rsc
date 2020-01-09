module Syntax

extend lang::std::Layout;
extend lang::std::Id;

/*
 * Concrete syntax of QL
 */

start syntax Form 
  = "form" Id name "{" Question* qs "}"; 

// TODO: question, computed question, block, if-then-else, if-then
syntax Question
  = Str string Id name ":" Type t
  | Str string Id name ":" Type t "=" Expr expr //computed question
  | "if ("Expr expression") {" Block block "}"
  ; 

syntax Block
  = Question* thenpart
  | Question* ifpart"}" "else" "{" Block elsepart
  ;

// TODO: +, -, *, /, &&, ||, !, >, <, <=, >=, ==, !=, literals (bool, int, str)
// Think about disambiguation using priorities and associativity
// and use C/Java style precedence rules (look it up on the internet)
syntax Expr 
  = id: Id i \ "true" \ "false"
  | \bool: Bool b//??
  | \int: Int integer
  | bracket B: "("Expr e")"
  | neg: "-"Expr e
  | not: "!"Expr e
  > left (mul: Expr lhs "*" Expr rhs| div: Expr lhs "/" Expr rhs)
  > left (add: Expr lhs "+" Expr rhs| sub: Expr lhs "-" Expr rhs)
  > non-assoc(gt: Expr lhs "\>" Expr rhs | lt: Expr lhs "\<" Expr rhs
  	| leq: Expr lhs "\<=" Expr rhs | geq: Expr lhs "\>=" Expr rhs 
  	| eq: Expr lhs "==" Expr rhs | neq: Expr lhs "!=" Expr rhs)
  > left (and: Expr lhs "&&" Expr rhs)
  > left (or: Expr lhs "||" Expr rhs)
  ;
  
syntax Primary
  = Bool
  | Int
  | Str
  | Id \ "true" \ "false" // true/false are reserved keywords.
  ;
 
syntax Type
  = "boolean" | "integer";  
  
lexical Str = "\""![\n\"]*"\"";

lexical Int 
  = [0-9]+;

lexical Bool = "true" | "false";
