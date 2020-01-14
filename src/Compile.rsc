module Compile

import AST;
import Resolve;
import Eval;
import IO;
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

  return html(head(title("<f.name>")), 
  		body(
  			div(id(f.name),
  				div([question2html(q) | AQuestion q <- f.questions])
  			),
  			script(src(<f.src[extension="js"].file>))
  		));
}

HTML5Node questions2html(AQuestion question) {
  switch(question) {
	case ifquestion(AExpr ae, ABlock b):
		switch(b) {
			case ifblock(list[AQuestion] \if): 
			  if(/*eval(ae) == "true"*/ false) {
				for(qs <- \if) return questions2html(qs);
			  } else {
			  	return section(hidden("<ae>"));
			  }
			case ifelseblock(list[AQuestion] \if, list[AQuestion] \else):
			  if(/*eval(ae) == "true"*/ true) {
				for(qs <- \if) return questions2html(qs);
			  } else {
				for(qs <- \else) return questions2html(qs);
			  }
		}
	case question(str q, AId ai, AType at):
	  if(at.name == "integer") {   
	  	return li(label("<q>"), input(\type("number"), name(ai.name), id(ai.name)));
	  } else if (at.name == "boolean") {
	  	return li(label("<q>"), input(\type("radio"), name(ai.name), id(ai.name), \value("yes")), "yes", input(\type("radio"), name(ai.name), id(ai.name), \value("no")), "no");
	  } else {
	  	return li(label("<q>"), input(name(ai.name), id(ai.name)));
	  }
	case compquestion(str q, AId ai, AType at, AExpr ae): 
	  return li(label("<q>"), p(/*<eval(ae)>*/"answer:"));
	}
}

str form2js(AForm f) { //string templates
  return "function getInputs() {
  		 '  document.getElementById(\"result\").innerHTML = \"clicked\";	
  		 ' <for(/question(str q, AId ai, AType t) := f){>
  		 '	 var <ai.name>value = document.getElementById(<ai.name>).value;
  		 '<}>
  		 '}
  		 ";
}
