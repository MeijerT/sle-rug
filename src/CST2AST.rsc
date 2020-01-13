module CST2AST

import Syntax;
import AST;

import ParseTree;
import String;

/*
 * Implement a mapping from concrete syntax trees (CSTs) to abstract syntax trees (ASTs)
 *
 * - Use switch to do case distinction with concrete patterns (like in Hack your JS) 
 * - Map regular CST arguments (e.g., *, +, ?) to lists 
 *   (NB: you can iterate over * / + arguments using `<-` in comprehensions or for-loops).
 * - Map lexical nodes to Rascal primitive types (bool, int, str)
 * - See the ref example on how to obtain and propagate source locations.
 */

AForm cst2ast(start[Form] sf) {
  Form f = sf.top; // remove layout before and after form
  return form("<f.name>", [cst2ast(q) | q <- f.qs], src=f@\loc); 
}

AQuestion cst2ast(Question q) {
  switch (q) {
    case (Question)`<Str q1> <Id x> : <Type t>`: return question("<q1>", id("<x>", src=x@\loc), cst2ast(t));
    case (Question)`<Str q1> <Id x> : <Type t> = <Expr e>`: return compquestion("<q1>", id("<x>", src=x@\loc), cst2ast(t), cst2ast(e));
    case (Question) `if (<Expr e>) { <Block b> }`: return ifquestion(cst2ast(e), cst2ast(b));
    default: throw "Unhandled expression: <e>";
  }
}

ABlock cst2ast(Block b) {
  switch (b) {
  	case (Block) `<Question* ifpart> } else { <Question* elsepart>`: return ifelseblock([cst2ast(q) | q <- ifpart], [cst2ast(q) | q <- elsepart]);
  	case (Block) `<Question* qs>`: return ifblock([cst2ast(q) | q <- qs]); //list of questions??
  	default: throw "Unhandled expression: <e>";
  }
}

AExpr cst2ast(Expr e) {
  switch (e) {
    case (Expr) `<Int i>` : return \int(toInt("<i>"));
    case (Expr) `<Id x>`: return ref(id("<x>", src=x@\loc), src=x@\loc);
    case (Expr) `<Bool b>`: return \bool(\bool("<b>"));
    case (Expr) `(<Expr e>)`: return B(cst2ast(e));
    case (Expr) `!<Expr e>`: return notExpr(cst2ast(e));
    case (Expr) `-<Expr e>`: return negExpr(cst2ast(e));
    case (Expr) `<Expr lhs> + <Expr rhs>`: return add(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> - <Expr rhs>`: return sub(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> * <Expr rhs>`: return mul(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> / <Expr rhs>`: return div(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> \< <Expr rhs>`: return lt(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> \> <Expr rhs>`: return gt(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> \<= <Expr rhs>`: return leq(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> \>= <Expr rhs>`: return geq(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> == <Expr rhs>`: return eq(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> != <Expr rhs>`: return neq(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> && <Expr rhs>`: return and(cst2ast(lhs), cst2ast(rhs));
    case (Expr) `<Expr lhs> || <Expr rhs>`: return or(cst2ast(lhs), cst2ast(rhs));
    default: throw "Unhandled expression: <e>";
  }
}

AType cst2ast(Type t) {
  switch (t) {
    case (Type) `boolean`: return \type("boolean");
    case (Type) `integer`: return \type("integer");
    default: throw "Unhandled expression: <e>";
  }
}

ABool cst2ast(Bool b) {
  switch (b) {
    case (Bool) `true`: return \type("true");
    case (Bool) `false`: return \type("false");
    default: throw "Unhandled expression: <e>";
  }
}
