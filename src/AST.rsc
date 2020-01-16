module AST

/*
 * Define Abstract Syntax for QL
 *
 * - complete the following data types
 * - make sure there is an almost one-to-one correspondence with the grammar
 */

data AForm(loc src = |tmp:///|)
  = form(str name, list[AQuestion] questions)
  ; 

data AQuestion(loc src = |tmp:///|)
  = question(str q, AId ai, AType at)
  | compquestion(str q, AId ai, AType at, AExpr ae)
  | ifquestion(AExpr check, list[AQuestion] ifpart)
  | ifelsequestion(AExpr check, list[AQuestion] ifpart, list[AQuestion] elsepart)
  ; 

data AExpr(loc src = |tmp:///|) //can we leave bracket?
  = ref(AId id)
  | \bool(bool boolean)
  | \int(int integer)
  | \str(str string)
  | B(AExpr e)
  | notExpr(AExpr e) //"!"Expr
  | negExpr(AExpr e) //"-" Expr
  | mul(AExpr lhs, AExpr rhs)
  | div(AExpr lhs, AExpr rhs)
  | add(AExpr lhs, AExpr rhs)
  | sub(AExpr lhs, AExpr rhs)
  | gt(AExpr lhs, AExpr rhs)
  | lt(AExpr lhs, AExpr rhs)
  | leq(AExpr lhs, AExpr rhs)
  | geq(AExpr lhs, AExpr rhs)
  | eq(AExpr lhs, AExpr rhs)
  | neq(AExpr lhs, AExpr rhs)
  | and(AExpr lhs, AExpr rhs)
  | or(AExpr lhs, AExpr rhs)
  ;

data AId(loc src = |tmp:///|) = id(str name);

data AType(loc src = |tmp:///|) = \type(str name);

/*data AInt(loc src = |tmp:///|)
  = \int(str integer);*///hangt af van cst2ast