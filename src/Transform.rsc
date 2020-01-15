module Transform

import Syntax;
import Resolve;
import AST;

import ParseTree;
import CST2AST;
import IO;

/* 
 * Transforming QL forms
 */
 
 
/* Normalization:
 *  wrt to the semantics of QL the following
 *     q0: "" int; 
 *     if (a) { 
 *        if (b) { 
 *          q1: "" int; 
 *        } 
 *        q2: "" int; 
 *      }
 *
 *  is equivalent to
 *     if (true) q0: "" int;
 *     if (true && a && b) q1: "" int;
 *     if (true && a) q2: "" int;
 *
 * Write a transformation that performs this flattening transformation.
 *
 */

AForm testflatten() {
  return flatten(cst2ast(parse(#start[Form],|project://sle-rug/examples/test.myql|)));
}

list[AQuestion] flattenq(AQuestion q, AExpr e) {
  list[AQuestion] trans = [];
  switch(q) {
    case question(str label, AId aid, AType at): {
      return [ifquestion(e, [question(label, aid, at)])];
    }
    case compquestion(str label, AId aid, AType at, AExpr ae): {
      return [ifquestion(e, [compquestion(label, aid, at, ae)])];
    }
    case ifquestion(AExpr check, list[AQuestion] ifpart): {
      for (qif <- ifpart) {
        trans += flattenq(qif, and(e,check));
      }
    }
    case ifelsequestion(AExpr check, list[AQuestion] ifpart, list[AQuestion] elsepart): {
      for (qif <- ifpart) {
        trans += flattenq(qif, and(e,check));
      }
      for (qif <- elsepart) {
        trans += flattenq(qif, and(e,notExpr(check)));
      }
    }
    default: {
      print("Didn\'t recognize a question type\n");
      print(q);
      print("\n");
    }
  }
  return trans;
}

AForm flatten(AForm f) {
  list[AQuestion] qs = f.questions;
  list[AQuestion] trans = [];
  for (q <- qs) {
    switch(q) {
      case question(str label, AId aid, AType at): {
        trans += ifquestion(\bool(\bool("true")), [question(label, aid, at)]);
      }
      case compquestion(str label, AId aid, AType at, AExpr ae): {
        trans += ifquestion(\bool(\bool("true")), [compquestion(label, aid, at, ae)]);
      }
      case ifquestion(AExpr check, list[AQuestion] ifpart): {
        for (qif <- ifpart) {
          trans += flattenq(qif, check);
        }
      }
      case ifelsequestion(AExpr check, list[AQuestion] ifpart, list[AQuestion] elsepart): {
        for (qif <- ifpart) {
          trans += flattenq(qif, check);
        }
        for (qif <- elsepart) {
          trans += flattenq(qif, notExpr(check));
        }
      }
      default: {
        print("Didn\'t recognize a question type\n");
        print(q);
        print("\n");
      }
    }
  }
  f.questions = trans;
  return f;
}

/* Rename refactoring:
 *
 * Write a refactoring transformation that consistently renames all occurrences of the same name.
 * Use the results of name resolution to find the equivalence class of a name.
 *
 */
 
start[Form] testrename() {
  f = parse(#start[Form], |project://sle-rug/examples/cyclic.myql|);
  AForm af = cst2ast(f);
  return rename(f, |project://sle-rug/examples/cyclic.myql|(154,12,<8,6>,<8,18>), "test", resolve(af));
}

bool compareLocs(str oldName, RefGraph rg, loc x) {
  if (x in rg.defs[oldName]) {
    print("Found definition!");
    return true;
  }
  if (oldName in rg.uses[x]) {
    return true;
  }
  return false;
}
 
start[Form] rename(start[Form] f, loc useOrDef, str newName, RefGraph rg) {
  str oldName;
  if (<str d, loc def> <- rg.defs, def == useOrDef) {
    oldName = d;
  } else if (<loc use, str d> <- rg.uses, use == useOrDef) {
    oldName = d;
  } else {
    print("loc not found\n");
  }
  
  Id newName2 = [Id]newName;
  return visit (f) {
    case (Expr) `<Id x>` => (Expr) `<Id newName2>`
    when
      compareLocs(oldName, rg, x@\loc)
    case (Question) `<Str q1> <Id x> : <Type t>` => (Question) `<Str q1> <Id newName2> : <Type t>`
    when
      compareLocs(oldName, rg, x@\loc)
    case (Question )`<Str q1> <Id x> : <Type t> = <Expr e>` => (Question) `<Str q1> <Id newName2> : <Type t> = <Expr e>`
    when
      compareLocs(oldName, rg, x@\loc)
    default:
      ;
  }
}
