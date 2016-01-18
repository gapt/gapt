import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

val eqLemma = new Lemma(
	Sequent(Seq("eq1" -> parseFormula("u = v"), "eq2" -> parseFormula("x = y"), "a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	use(eqL("eq1", "a"))
	use(eqR("eq2", "b"))
}

val defLemma = new Lemma(
	Sequent(Seq("a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	use(defL("a", parseFormula("P(a) -> Q(a)")))
	use(defR("b", parseFormula("P(b) | Q(b)")))
}