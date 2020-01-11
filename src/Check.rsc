module Check

import AST;
import Resolve;
import Message; // see standard library
import IO;

import List;

data Type
  = tint()
  | tbool()
  | tstr()
  | tunknown()
  ;

// the type environment consisting of defined questions in the form 
alias TEnv = rel[loc def, str name, str label, AType \type];//changed to AType

// To avoid recursively traversing the form, use the `visit` construct
// or deep match (e.g., `for (/question(...) := f) {...}` ) 
TEnv collect(AForm f) {
  rel[loc def, str name, str label, AType \type] r = {};
  for (/question(str q, AId i, AType t) := f) {
  	r += {<i.src, i.name, q, t>};
  }
  for (/compquestion(str q, AId i, AType t, AExpr e) := f) {
  	r += {<i.src, i.name, q, t>};
  }
  return r;
}

set[Message] check(AForm f, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  //print("Regular questions:\n");
  for (/question(str q, AId ai, AType at) := f) {
    //print(q + "\n");
  	msgs += dupl(tenv, useDef, q, ai.src, ai, at);
  }
  //print("Computed questions:\n");
  for (/compquestion(str q, AId ai, AType at, AExpr ae) := f) {
    //print(q + "\n");
    msgs += duplcomp(tenv, useDef, q, ai.src, ai, at, ae);
  }
  
  for (/ifquestion(AExpr ae, ABlock _) := f) {
    //print(q + "\n");
    Type ae_type = typeOf(ae, tenv, useDef);
    if (ae_type != tbool()) {
      msgs += {error("Expected boolean expression, but got something else", ae.src)};
    }
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
      msgs += dupl(tenv, useDef, label, q.src, aid, at);
    case compquestion(str label, AId aid, AType at, AExpr ae):
      msgs += duplcomp(tenv, useDef, label, q.src, at, ae);
  };
  
  return msgs;
}

set[Message] dupl(TEnv tenv, UseDef useDef, str label, loc q, AId ai, AType at) {
  //print("Checking duplicates for a regular question\n");
  set[Message] msgs = {};
  list[loc] labeloccs = [d | <d, _, l, _> <- tenv, l == label];
  if (size(labeloccs) > 1) {
    msgs += warning("Duplicate question", q);
  }
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  return msgs;
}

set[Message] duplcomp(TEnv tenv, UseDef useDef, str label, loc q, AId ai, AType at, AExpr ae) {
  //print("Checking duplicates for a computed question\n");
  set[Message] msgs = {};
  list[loc] labeloccs = [d | <d, _, l, _> <- tenv, l == label];
  if (size(labeloccs) > 1) {
    msgs += {warning("Duplicate question", q)};
  }
  //the declared type computed questions should match the type of the expression.
  msgs += {error("Type of question does not match type of expression", ai.src)
   | (at.name == "integer" && typeOf(ae, tenv, useDef) != tint())
   || (at.name == "boolean" && typeOf(ae, tenv, useDef) != tbool()) };
   
  // produce an error if there are declared questions with the same name but different types.
  //[d | <d, _, l, _> <- tenv, l == label];
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  
  msgs += check(ae, tenv, useDef);
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
        if (t == "boolean") {
        	return tbool();
        } else if (t == "integer") {
        	return tint();
        } else if (t == "string") {
        	return tstr();
        };
        return tunkown();
      } else {
        return tunknown();
      }
    // etc.
    case \bool(ABool b):
      return tbool();
    case \int(AInt i):
      return tint();
    
    case notExpr(AExpr e):
      return TypeOf(e);
    case negExpr(AExpr e):
      return TypeOf(e);
    case mul(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tint() && TypeOf(rhs) == tint()) {
      	println(rhs);
      	return tint();
      } else {
      	println("Expected int but wasn\'t");
      	println(rhs);
        return tunknown();
      }
    case div(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tint() && TypeOf(rhs) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    case add(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tint() && TypeOf(rhs) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    case sub(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tint() && TypeOf(rhs) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    
    case gt(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case lt(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case leq(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case geq(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case eq(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case neq(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case and(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case or(AExpr lhs, AExpr rhs):
      if (TypeOf(lhs) == tbool() && TypeOf(rhs) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    default:
      return tunknown();
  }
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
 
 

