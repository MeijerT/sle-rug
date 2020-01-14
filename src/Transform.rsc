module Transform

import Syntax;
import Resolve;
import AST;

import Syntax;
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
 
AForm flatten(AForm f) {
  list[AQuestion] qs = f.questions;
  list[AQuestion] trans = [];
  
  return f;
}

/* Rename refactoring:
 *
 * Write a refactoring transformation that consistently renames all occurrences of the same name.
 * Use the results of name resolution to find the equivalence class of a name.
 *
 */
 
start[Form] testrename() {
  f = parse(#start[Form], |project://SLE/examples/cyclic.myql|);
  AForm af = cst2ast(f);
  return rename(f, |project://SLE/examples/cyclic.myql|(154,12,<8,6>,<8,18>), "test", resolve(af));
}

bool compareLocs(str oldName, RefGraph rg, loc x) {
  if (<oldName, loc def> <- rg.defs, def == x) {
    return true;
  } else if (<use, oldName> <- rg.uses, loc use := x, <use, def> <- rg.useDef) {
    return true;
  }
  print("it was false\n");
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
    default:
      ;
   }
 } 
 
 
 

