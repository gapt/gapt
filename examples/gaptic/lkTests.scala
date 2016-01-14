import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val eqLemma = new Lemma(
	Sequent(Seq("eq1" -> parseFormula("u = v"), "eq2" -> parseFormula("x = y"), "a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	use(EqualityLeftTactic("eq1", "a"))
	use(EqualityRightTactic("eq2", "b"))
}

val defLemma = new Lemma(
	Sequent(Seq("a" -> parseFormula("P(u) -> Q(u)")), Seq("b" -> parseFormula("P(x) & Q(x)")))
) {
	use(DefinitionLeftTactic("a", parseFormula("P(a) -> Q(a)")))
	use(DefinitionRightTactic("b", parseFormula("P(b) | Q(b)")))
}