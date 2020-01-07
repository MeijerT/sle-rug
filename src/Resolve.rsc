module Resolve

import AST;

/*
 * Name resolution for QL
 */ 


// modeling declaring occurrences of names
alias Def = rel[str name, loc def, str \type];

// modeling use occurrences of names
alias Use = rel[loc use, str name];

alias UseDef = rel[loc use, loc def];

// the reference graph
alias RefGraph = tuple[
  Use uses, 
  Def defs, 
  UseDef useDef
]; 

RefGraph resolve(AForm f) = <us, ds, us o ds>
  when Use us := uses(f), Def ds := defs(f);

Def defs(AForm f) {
  return {<x.name, x.src, t.name> | /question(str _, AId x, AType t) := f}
    + {<x.name, x.src, t.name> | /compquestion(str _, AId x, AType t, _) := f}
    ;
}

Use uses(AForm f) {
  return {<x.src, x.name> | /ref(str _, AId x) := f};
}