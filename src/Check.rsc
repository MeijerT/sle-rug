module Check

import AST;
import Resolve;
import Message; // see standard library
import IO;

import List;

import CST2AST;
import ParseTree;
import Syntax;

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

set[Message] testcheck(loc q) {
  aq = cst2ast(parse(#start[Form], q));
  q_tenv = collect(aq);
  print("Type Environment:\n");
  print(q_tenv);
  print("\n\n");
  return check(aq, collect(aq), resolve(aq)[2]);
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
  Type to = typeOf(ae, tenv, useDef);
  msgs += {error("Type of question does not match type of expression", ai.src)
   | to != str2type(at.name)};
  print("Question " + label + " has type ");
  print(to);
  print(" instead of ");
  print(str2type(at.name));
  print(".\n");
  // produce an error if there are declared questions with the same name but different types.
  //[d | <d, _, l, _> <- tenv, l == label];
  msgs += {error("Question with same name but different type", q) | <d, n, _, t> <- tenv, ai == n, at != t};
  
  msgs += check(ae, tenv, useDef);
  return msgs;
}

Type str2type(str s) {
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
      print("here\n");
      msgs += { error("Undeclared question", e.src) | useDef[e.src] == {} };
      if (size([<_,"<x>",_,_> <- tenv]) == 0) {
        msgs += {error("Undeclared variable", e.src)};
      };
    }
    case notExpr(AExpr e):
      msgs += { error("Not type compatible", e.src) | typeOf(e, tenv, useDef) != tbool() };
    case negExpr(AExpr e):
      msgs += { error("Not type compatible", e.src) | typeOf(e, tenv, useDef) != tint() };
    case mul(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tint() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tint() };
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
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case lt(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case leq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case geq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case eq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case neq(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case and(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    case or(AExpr lhs, AExpr rhs):
      msgs += { error("Not type compatible", e.src) | typeOf(lhs, tenv, useDef) != tbool() }
      + { error("Not type compatible", e.src) | typeOf(rhs, tenv, useDef) != tbool() };
    
    default: {
      print("Did not recognize expression: ");
      print(e.src);
      print("\n");
    }
  }
  
  return msgs; 
}

Type typeOf(AExpr e, TEnv tenv, UseDef useDef) {
  switch (e) {
    case ref(AId x): {
      loc x_loc = e.src;
      if (<x_loc, d> <- useDef, <loc d, "<x>", _, AType t> <- tenv) {
        if ("<t>" == "boolean") {
        	return tbool();
        } else if ("<t>" == "integer") {
        	return tint();
        } else if ("<t>" == "string") {
        	return tstr();
        };
        return tunkown();
      } else {
        print("Did not find variable\n");
        return tunknown();
      }
    }
    // etc.
    case \bool(ABool b):
      return tbool();
    case \int(AInt i):
      return tint();
    
    case notExpr(AExpr e):
      return typeOf(e, tenv, useDef);
    case negExpr(AExpr e):
      return typeOf(e, tenv, useDef);
    case mul(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tint() && typeOf(rhs, tenv, useDef) == tint()) {
      	println(rhs);
      	return tint();
      } else {
      	println("Expected int but wasn\'t");
      	println(rhs);
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
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case lt(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case leq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case geq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case eq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
      }
    case neq(AExpr lhs, AExpr rhs):
      if (typeOf(lhs, tenv, useDef) == tbool() && typeOf(rhs, tenv, useDef) == tbool()) {
      	return tbool();
      } else {
        return tunknown();
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
