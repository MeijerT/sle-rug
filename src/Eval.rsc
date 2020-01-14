module Eval

import AST;
import Resolve;

/*
 * Implement big-step semantics for QL
 */
 
// NB: Eval may assume the form is type- and name-correct.

import IO;

import List;

import CST2AST;
import ParseTree;
import Syntax;

// Semantic domain for expressions (values)
data Value
  = vint(int n)
  | vbool(bool b)
  | vstr(str s)
  ;

// The value environment
alias VEnv = map[str name, Value \value];

// Modeling user input
data Input
  = input(str question, Value \value);

VEnv testeval() {
  AForm atax = cst2ast(parse(#start[Form],|project://SLE/examples/test.myql|));
  return eval(atax, input("\"mijn vraag?\"", vstr("sfasfef?")), initialEnv(atax));
}

  
// produce an environment which for each question has a default value
// (e.g. 0 for int, "" for str etc.)
VEnv initialEnv(AForm f) {
  map[str name, Value \value] m = ();
  for (/question(str q, AId i, AType t) := f) {
    if (t.name == "integer") {
      m = (i.name:\vint(0)) + m;
    } else if (t.name == "boolean") {
      m = (i.name:\vbool(false)) + m;
    } else {
      m = (i.name:\vstr("")) + m;
    }
  }
  for (/compquestion(str q, AId i, AType t, AExpr ae) := f) {
    if (t.name == "integer") {
      m = (i.name:\vint(0)) + m;
    } else if (t.name == "boolean") {
      m = (i.name:\vbool(false)) + m;
    } else {
      m = (i.name:\vstr("")) + m;
    }
  }
  return m;
}


// Because of out-of-order use and declaration of questions
// we use the solve primitive in Rascal to find the fixpoint of venv.
VEnv eval(AForm f, Input inp, VEnv venv) {
  return solve (venv) {
    venv = evalOnce(f, inp, venv);
  }
}

VEnv evalOnce(AForm f, Input inp, VEnv venv) {//not sure what we need to do here
  map[str name, Value \value] m = ();
  for (/question(str q, AId ai, AType at) := f) {
    if (inp.question == q) {
      return m = eval(question(q, ai, at), inp, venv) + m;
  	}
  }
  for (/compquestion(str q, AId ai, AType at, AExpr ae) := f) {
    if (inp.question == q) {
  	  return m = eval(compquestion(q, ai, at, ae), inp, venv) + m;
  	}
  }
  for (/ifquestion(AExpr ae, ABlock ab) := f) {
  	m += eval(ifquestion(ae, ab), inp, venv);
  }
  return m;
}

VEnv eval(AQuestion q, Input inp, VEnv venv) {
  // evaluate conditions for branching,
  // evaluate inp and computed questions to return updated VEnv
  map[str name, Value v] m = ();
  switch(q) {
    case question(str label, AId aid, AType at): {
      if (inp.question == label) {
        if (at.name == "integer") {
          //integer
      	  m = (aid.name : vint(inp.\value.n)) + m;
        } else if (at.name == "boolean") {
      	  //boolean
          m = (aid.name : vbool(inp.\value.b)) + m;
        } else {
       	  //string
          m = (aid.name : vstr(inp.\value.s)) + m;
        }
      }
    }
    case compquestion(str label, AId aid, AType at, AExpr ae):
      if (inp.question == label) {
        if (at.name == "integer") {
      	  m = (aid.name : vint(inp.\value.n)) + m;
        } else if (at.name == "boolean") {
      	  //boolean
          m = (aid.name : vbool(inp.\value.b)) + m;
        } else {
          //string
          m = (aid.name : vstr(inp.\value.s)) + m;
        }
      }
    case ifquestion(AExpr ae, ABlock b):
      if (eval(ae, venv).b) {
      	switch(b) {
      	  case ifblock(list[AQuestion] questions): 
      	  	if(eval(ae, venv).b) {
      	  	  m = ( eval(qn, inp, venv).name :  eval(qn, inp, venv).\value | qn <- questions ) + m;
      	  	}
      	  case ifelseblock(list[AQuestion] \if, list[AQuestion] \else): 
      	    if(eval(ae, venv).b) {
      	  	  m = ( eval(qn, inp, venv).name : eval(qn, inp, venv).\value | qn <- \if ) + m;
      	  	} else { 
      	  	  m = ( eval(qn, inp, venv).name : eval(qn, inp, venv).\value | qn <- \else ) + m;
      	  	}
      	}
      }
  };
  return m;
}

Value eval(AExpr e, VEnv venv) {
  switch (e) {
    case ref(str x): return venv[x];
    
    case notExpr(AExpr e): 
    	if(eval(e, venv).b) { 
    	  return vbool(false); 
    	} else {
    	  return vbool(true);
    	}
      
    case negExpr(AExpr e): return vint(eval(e, venv).n * -1);
      
    case mul(AExpr lhs, AExpr rhs): return vint(eval(lhs, venv).n * eval(rhs, venv).n);
      
    case div(AExpr lhs, AExpr rhs): return vint(eval(lhs, venv).n / eval(rhs, venv).n);
      
    case add(AExpr lhs, AExpr rhs): return vint(eval(lhs, venv).n + eval(rhs, venv).n);
      
    case sub(AExpr lhs, AExpr rhs): return vint(eval(lhs, venv).n - eval(rhs, venv).n);
      
    
    case gt(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n > eval(rhs,venv).n);
      
    case lt(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n > eval(rhs,venv).n);
      
    case leq(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n <= eval(rhs,venv).n);
      
    case geq(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n >= eval(rhs,venv).n);
      
    case eq(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n == eval(rhs,venv).n);
      
    case neq(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).n != eval(rhs,venv).n);
      
    case and(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).b && eval(rhs, venv).b);
      
    case or(AExpr lhs, AExpr rhs): return vbool(eval(lhs, venv).b || eval(rhs, venv).b);
    
    default: throw "Unsupported expression <e>";
  }
}