module Check

import AST;
import Resolve;
import Message; // see standard library

data Type
  = tint()
  | tbool()
  | tstr()
  | tunknown()
  ;

// the type environment consisting of defined questions in the form 
alias TEnv = rel[loc def, str name, str label, Type \type];

// To avoid recursively traversing the form, use the `visit` construct
// or deep match (e.g., `for (/question(...) := f) {...}` ) 
TEnv collect(AForm f) {
  return {
  	for (/question(str q, AId i, AType t) := f) {
  	  append [i.src, i.name, q, t.name];
  	}
  	for (/compquestion(str q, AId i, AType t, AExpr e) := f) {
  	  append [i.src, i.name, q, t.name];
  	}
  };
}

set[Message] check(AForm f, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  for (/question(str q, AId i, AType t) := f) {
  	  msgs += check(question(q, i, t), tenv, useDef);
  }
  for (/compquestion(str q, AId i, AType t, AExpr e) := f) {
  	 msgs += check(question(q, i, t), tenv, useDef);
  }
  // produce an error if there are declared questions with the same name but different types.

  return msgs;
}

// - produce an error if there are declared questions with the same name but different types.
// - duplicate labels should trigger a warning 
// - the declared type computed questions should match the type of the expression.
set[Message] check(AQuestion q, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  
  // duplicate labels
  switch(q) {
    case question(str label, AId aid, AType at):
      msgs += dupl(tenv, useDef, label, q.src, ai, at);
    case compquestion(str label, AId aid, AType at, AExpr ae):
      msgs += duplcomp(tenv, useDef, label, q.src, at, ae);
  };
  
  
  
  return msgs;
}

set[Message] dupl(TEnv tenv, UseDef useDef, str label, loc q, AId ai, AType at) {
  set[Message] msgs = {};
  list[loc] labeloccs = [d | <d, _, l, _> <- tenv, l == label];
  if (length(labeloccs) > 1) {
    msgs += warning("Duplicate question", q);
  }
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  return msgs;
}

set[Message] duplcomp(TEnv tenv, UseDef useDef, str label, loc q, AId, ai, AType at, AExpr ae) {
  set[Message] msgs = {};
  list[loc] labeloccs = [d | <d, _, l, _> <- tenv, l == label];
  if (length(labeloccs) > 1) {
    msgs += { warning("Duplicate question", q)};
  }
  //the declared type computed questions should match the type of the expression.
  msgs += {error("type of question does not match type of expression", q)
   | (at.name == "integer" && typeOf(ae, tenv, useDef) != tint())
   || (at.name == "boolean" && typeOf(ae, tenv, useDef) != tbool()) };
   
  // produce an error if there are declared questions with the same name but different types.
  //[d | <d, _, l, _> <- tenv, l == label];
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  return msgs;
}

// Check operand compatibility with operators.
// E.g. for an addition node add(lhs, rhs), 
//   the requirement is that typeOf(lhs) == typeOf(rhs) == tint()
set[Message] check(AExpr e, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  
  switch (e) {
    case ref(str x, src = loc u):
      msgs += { error("Undeclared question", u) | useDef[u] == {} };
    
    case notExpr(AExpr e):
      msgs += { error("Not type compatible", e) | typeOf(e, tenv, useDef) != tbool() };
    case negExpr(AExpr e):
      msgs += { error("Not type compatible", e) | typeOf(e, tenv, useDef) != tint() };
    case mul(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tint() };
    case div(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tint() };
    case add(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tint() };
    case sub(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tint() };
    
    case gt(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case lt(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case leq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case geq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case eq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case neq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case and(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
    case or(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e) | typeOf(rhs, tenv, useDef) != tbool() };
  }
  
  return msgs; 
}

Type typeOf(AExpr e, TEnv tenv, UseDef useDef) {
  switch (e) {
    case ref(str x, src = loc u):  
      if (<u, loc d> <- useDef, <d, x, _, Type t> <- tenv) {
        return t;
      }
    // etc.
    case \bool(ABool b):
      return tbool();
    case \int(AInt i):
      return tint();
    
    case notExpr(AExpr e):
      return tbool();
    case negExpr(AExpr e):
      return tint();
    case mul(AExpr lhs, AExpr rhs):
      return tint();
    case div(AExpr lhs, AExpr rhs):
      return tint();
    case add(AExpr lhs, AExpr rhs):
      return tint();
    case sub(AExpr lhs, AExpr rhs):
      return tint();
    
    case gt(AExpr lhs, AExpr rhs):
      return tbool();
    case lt(AExpr lhs, AExpr rhs):
      return tbool();
    case leq(AExpr lhs, AExpr rhs):
      return tbool();
    case geq(AExpr lhs, AExpr rhs):
      return tbool();
    case eq(AExpr lhs, AExpr rhs):
      return tbool();
    case neq(AExpr lhs, AExpr rhs):
      return tbool();
    case and(AExpr lhs, AExpr rhs):
      return tbool();
    case or(AExpr lhs, AExpr rhs):
      return tbool();
  }
  return tunknown(); 
}

/* 
 * Pattern-based dispatch style:
 * 
 * Type typeOf(ref(str x, src = loc u), TEnv tenv, UseDef useDef) = t
 *   when <u, loc d> <- useDef, <d, x, _, Type t> <- tenv
 *
 * ... etc.
 * 
 * default Type typeOf(AExpr _, TEnv _, UseDef _) = tunknown();
 *
 */
 
 

