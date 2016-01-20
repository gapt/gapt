import at.logic.gapt.expr.FOLVar
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._

val drinker = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  exR(parseTerm("c"), "D1")
  impR("D1")
  allR(FOLVar("y_0"), "D1_2")
  exR(parseTerm("y_0"), "D2")
  impR("D2")
  allR(FOLVar("y_1"), "D2_2")
  axiomLog
}

val dualdrinker = Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))")), Nil )) {
  allL(parseTerm("c"), "D1")
  andL("D1")
  exL(FOLVar("y_0"))
  negL("D1_2")
  allL(parseTerm("y_0"), "D2")
  andL("D2")
  exL(FOLVar("y_1"))
  negL("D2_2")
  axiomLog
}

val drinker2 = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  exR(parseTerm("c"), "D1")
  impR
  allR
  exR(parseTerm("y"), "D2")
  impR
  allR
  axiomLog
}

val drinker3 = Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  exR(parseTerm("c"), "D1")
  impR
  allR
  exR(parseTerm("y"), "D2")
  impR
  allR
  axiom
}

val dualdrinker2 = Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))")), Nil )) {
  allL(parseTerm("c"), "D1")
  andL
  exL
  negL
  allL(parseTerm("y"), "D2")
  andL
  exL
  negL
  axiomLog
}