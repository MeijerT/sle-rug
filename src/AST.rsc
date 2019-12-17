module AST

/*
 * Define Abstract Syntax for QL
 *
 * - complete the following data types
 * - make sure there is an almost one-to-one correspondence with the grammar
 */

data AForm(loc src = |tmp:///|)
  = form(str name, list[AQuestion] questions)
  ; 

data AQuestion(loc src = |tmp:///|)
  = question(str q, AId, AExpr)
  | question(str q, AId, AType)
  ; 

data AExpr(loc src = |tmp:///|)
  = ref(AId id)
  ;

data AId(loc src = |tmp:///|)
  = id(str name);

data AType(loc src = |tmp:///|);

AForm implode(start[Form] f)
  = implode(f.top);

AForm implode((Form)`form <Id name> <Question* qs>`)
  = form("<name>", [ implode(q) | Question q <- qs ]);

AQuestion implode((Question)`state <Id quest> <Expr e>`)
  = question(id("<name>", src=name@\loc), implode(e));

AExpr implode((Expr)`ex <Expr lhs> <Opr op> <Expr rhs>`)
  = expr("<e>");
  