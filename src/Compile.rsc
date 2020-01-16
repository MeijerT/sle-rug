module Compile

import AST;
import Resolve;
import Eval;
import CST2AST;
import ParseTree;
import Check;
import Syntax;
import Transform;
import IO;
import List;
import lang::html5::DOM; // see standard library

/*
 * Implement a compiler for QL to HTML and Javascript
 *
 * - assume the form is type- and name-correct
 * - separate the compiler in two parts form2html and form2js producing 2 files
 * - use string templates to generate Javascript
 * - use the HTML5Node type and the `str toString(HTML5Node x)` function to format to string
 * - use any client web framework (e.g. Vue, React, jQuery, whatever) you like for event handling
 * - map booleans to checkboxes, strings to textfields, ints to numeric text fields
 * - be sure to generate uneditable widgets for computed questions!
 * - if needed, use the name analysis to link uses to definitions
 */

void compile(AForm f) {
  writeFile(f.src[extension="js"].top, form2js(f));
  writeFile(f.src[extension="html"].top, toString(form2html(f)));
}

HTML5Node form2html(AForm f) { 

  return html(
  		    head(title("<f.name>")
  		  ), 
  		  body(
  			div(id(f.name),
  			  div([questions2html(q) | q:AQuestion _ <- f.questions])
  			),
      		script(src(f.src[extension="js"].file))
  		  )
  		 );
}

HTML5Node questions2html(AQuestion question) {
  switch(question) {
	
	case ifquestion(AExpr ae, list[AQuestion] ifpart):
	  return div(
	  div([questions2html(q) | AQuestion q <- ifpart])
	  );
	
	case ifelsequestion(AExpr ae, list[AQuestion] ifpart, list[AQuestion] elsepart):
	  return div( 
	  div([id("ifpart" + expr2js(ae))] + [questions2html(q) | AQuestion q <- ifpart]), 
	  div([id("elsepart" + expr2js(ae))] + [questions2html(q) | AQuestion q <- elsepart])
	  );
	
	case question(str q, AId ai, AType at):
	  return div(
	  	id(ai.name),
        label(\for("<q>"), q),
        input(name(ai.name), id("input"+ai.name), type2attr(at))
      );
	
	case compquestion(str q, AId ai, AType at, AExpr ae): 
	  return div(
	  	id(ai.name),
        label(\for("<q>"), q),
        input(name(ai.name), id("input"+ai.name),type2attr(at), disabled("true"),readonly("true"))
      );
	}
}

HTML5Attr type2attr(AType t) {
  if(t.name == "integer") {
  	return \type("number");
  } else if (t.name == "boolean") {
  	return \type("checkbox");
  } else {
  	return \type("text");
  }
}

str defaultValues(AType t) {
  if(t.name == "boolean") {
  	return "false";
  } else if (t.name == "integer") {
  	return "0";
  } else {
  	return "\"\"";
  }
}

str form2js(AForm f) {
  list[str] formjs = [];
  formjs += ["var <ai.name> = document.getElementById(\'input<ai.name>\').<type2prop(t)>;" 
           | /question(_, AId ai, AType t) := f];
  
  formjs += ["//variable <ai.name>:
				document.getElementById(\'input<ai.name>\').<type2prop(t)> = <expr2js(ae)>;" 
           		| /compquestion(_, AId ai, AType t, AExpr ae) := f];

  return 
		"document.addEventListener(\'input\', function (evt) {
		'  updateForm();
		});
		updateForm();
		function updateForm() {
		'	<intercalate("\n", formjs + [form2js(q) | q <- f.questions])>
		}";
}

str form2js(ifquestion(AExpr check, list[AQuestion] ifpart)) {
  return 
"if (<expr2js(check)>) {
'  <for(q <- ifpart) {> 
'	<form2js(q, visible=true)>
   <}>
} else {
'  <for(q <- ifpart) {> 
'	<form2js(q, visible=false)>
   <}>
}";
}

str form2js(ifelsequestion(AExpr check, list[AQuestion] ifpart, list[AQuestion] elsepart)) {
  return 
"if (<expr2js(check)>) {
'	document.getElementById(\'ifpart<expr2js(check)>\').style.display = \"\";
'	document.getElementById(\'elsepart<expr2js(check)>\').style.display = \"none\";
'  <for(q <- ifpart) {> 
'	<form2js(q, visible=true)>
'   <}>
'   <for(q <- elsepart) {> 
'	<form2js(q, visible=false)>
'   <}>
} else {
'	document.getElementById(\'ifpart<expr2js(check)>\').style.display = \"none\";
'	document.getElementById(\'elsepart<expr2js(check)>\').style.display = \"\";
'  <for(q <- ifpart) {> 
'	<form2js(q, visible=false)>
'   <}>
'   <for(q <- elsepart) {> 
'	<form2js(q, visible=true)>
'   <}>
}";
}

str form2js(question(str label, AId id, AType tp), bool visible = true) {
  return "document.getElementById(\'<id.name>\').style.display = <visible ? "\"\"" : "\"none\"">;";
}

str form2js(compquestion(str label, AId id, AType tp, AExpr ae), bool visible = true) {
  return "document.getElementById(\'<id.name>\').style.display = <visible ? "\"\"" : "\"none\"">;";
}

str type2prop(AType t) {
  if(t.name == "boolean") {
    return "checked";
   } else {
     return "value";
   }
}

str expr2js(AExpr e) {
  switch (e) {
    case ref(AId x):
      return "<x.name>";
	case \int(int i):
      return "<i>";
    case \bool(bool b): 
      return "<b>";
    case \str(str s):
      return "\"<s>\"";
    case B(AExpr expr):
      return "(<expr2js(expr)>)";
    
    case notExpr(AExpr expr):
      return "(!<expr2js(expr)>)"; 
      
    case negExpr(AExpr expr):
      return "(-<expr2js(expr)>)";
      
    case mul(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> * <expr2js(rhs)>)";

    case div(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> / <expr2js(rhs)>)";

    case add(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> + <expr2js(rhs)>)";

    case sub(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> - <expr2js(rhs)>)";

    case gt(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> \> <expr2js(rhs)>)";

    case geq(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> \>= <expr2js(rhs)>)";

    case lt(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> \< <expr2js(rhs)>)";

    case leq(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> \<= <expr2js(rhs)>)";

    case eq(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)>) == (<expr2js(rhs)>)";

    case neq(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)>) != (<expr2js(rhs)>)";

    case and(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> && <expr2js(rhs)>)";

    case or(AExpr lhs, AExpr rhs):
      return "(<expr2js(lhs)> || <expr2js(rhs)>)";
      
    default: throw "unsupported expression <e>";

  }
}