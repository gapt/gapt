import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._

val eqLemma = Lemma(
	Sequent(Seq("eq1" -> parseFormula("u = v"), "eq2" -> parseFormula("x = y"), "a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	eqL("eq1", "a")
	eqR("eq2", "b")
}

val defLemma = Lemma(
	Sequent(Seq("a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	defL("a", parseFormula("P(a) -> Q(a)"))
	defR("b", parseFormula("P(b) | Q(b)"))
}