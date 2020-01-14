module Check

import AST;
import Resolve;
import Message; // see standard library
import IO;

import List;

import CST2AST;
import ParseTree;
import Syntax;

data CType
  = tint()
  | tbool()
  | tstr()
  | tunknown()
  ;

// the type environment consisting of defined questions in the form 
alias TEnv = rel[loc def, str name, str label, CType ct];//changed to AType

// To avoid recursively traversing the form, use the `visit` construct
// or deep match (e.g., `for (/question(...) := f) {...}` ) 
TEnv collect(AForm f) {
  rel[loc def, str name, str label, CType ct] r = {};
  for (/question(str q, AId i, AType t) := f) {
  	r += {<i.src, i.name, q, str2type(t.name)>};
  }
  for (/compquestion(str q, AId i, AType t, AExpr e) := f) {
  	r += {<i.src, i.name, q, str2type(t.name)>};
  }
  return r;
}

Type atype2type(AType t) {
  if ("<t>" == "integer") {
    return tint();
  } else if ("<t>" == "boolean") {
    return tbool();
  } else if ("<t>" == "string") {
    return tstr();
  }
  return tunknown();
}

set[Message] testcheck(loc q) {
  aq = cst2ast(parse(#start[Form], q));
  //q_tenv = collect(aq);
  //print("Type Environment:\n");
  //print(q_tenv);
  //print("\n\n");
  return check(aq, collect(aq), resolve(aq)[2]);
}

set[Message] check(AForm f, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  //print("Regular questions:\n");
  for (/question(str q, AId ai, AType at) := f) {
    print(q + "\n");
  	msgs += dupl(tenv, useDef, q, ai.src, ai, at);
  }
  //print("Computed questions:\n");
  for (/compquestion(str q, AId ai, AType at, AExpr ae) := f) {
    //print(q + "\n");
    msgs += duplcomp(tenv, useDef, q, ai.src, ai, at, ae);
  }
  
  for (/ifquestion(AExpr ae, _) := f) {
    //print(q + "\n");
    CType ae_type = typeOf(ae, tenv, useDef);
    if (ae_type != tbool() && ae_type != tunknown()) {
      msgs += {error("Expected boolean expression, but got something else", ae.src)};
    }
    msgs += check(ae, tenv, useDef);
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
  CType to = typeOf(ae, tenv, useDef);
  msgs += {error("Type of question does not match type of expression. Expected: " + at.name + ", got: " + ctype2str(to), ai.src)
   | to != str2type(at.name)};
  // produce an error if there are declared questions with the same name but different types.
  //[d | <d, _, l, _> <- tenv, l == label];
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  
  msgs += check(ae, tenv, useDef);
  return msgs;
}

str ctype2str(CType t) {
  if (t == tint()) {
    return "integer";
  } else if (t == tbool()) {
    return "boolean";
  } else if (t == tstr()) {
    return "string";
  }
  return "unknown";
}

CType str2type(str s) {
  switch (s) {
    case "boolean":
      return tbool();
    case "integer":
      return tint();
    case "string":
      return tstr();
    default:
      return tunknown();
  }
}

// Check operand compatibility with operators.
// E.g. for an addition node add(lhs, rhs), 
//   the requirement is that typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef) == tint()
set[Message] check(AExpr e, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  switch (e) {
    case ref(AId x): {
      msgs += { error("Undefined variable", e.src) | useDef[e.src] == {} };
    }
    
    case \int(AInt e): {
      return msgs;
    }
    
    case \bool(ABool e): {
      return msgs;
    }
    
    case \str(AStr e): {
      return msgs;
    }
    
    case B(AExpr e):
      msgs += check(e, tenv, useDef);
    
    case notExpr(AExpr e):
      msgs += { error("Not type compatible", e.src) | typeOf(e, tenv, useDef) != tbool() };
    case negExpr(AExpr e):
      msgs += { error("Not type compatible", e.src) | typeOf(e, tenv, useDef) != tint() };
    
    case mul(AExpr lhs, AExpr rhs): {
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    }
    case div(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case add(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case sub(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    
    case gt(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case lt(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case leq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case geq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case eq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
    case neq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) != typeOf(rhs, tenv, useDef)) {
        msgs += { error("Not type compatible", e.src) };
      }
    
    case and(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case or(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    
    default: {
      msgs += { error("Expression not recognized", e.src) };
    }
  }
  
  return msgs; 
}

CType typeOf(AExpr e, TEnv tenv, UseDef useDef) {
  switch (e) {
    case ref(id(_, src = loc u)): {
      if (<u, loc d> <- useDef, <d, x, _, CType t> <- tenv) {
        return t;
      } else {
        return tunknown();
      }
    }
    // etc.
    case \bool(ABool b):
      return tbool();
    case \int(AInt i):
      return tint();
    case \str(AStr s):
      return tstr();
    
    case B(AExpr e):
      return typeOf(e, tenv, useDef);
    
    case notExpr(AExpr e):
      return typeOf(e, tenv, useDef);
    case negExpr(AExpr e):
      return typeOf(e, tenv, useDef);
    case mul(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    case div(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    case add(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    case sub(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tint();
      } else {
        return tunknown();
      }
    
    case gt(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case lt(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case leq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case geq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case eq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
      	return tbool();
      } else {
        return tunknown();
      }
    case neq(AExpr lhs, AExpr rhs): {
      if (typeOf(lhs, tenv, useDef) == typeOf(rhs, tenv, useDef)) {
      	return tbool();
      } else {
        return tunknown();
      }
    }
    case and(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case or(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
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