import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val decomposeLemma = new Lemma(
	Sequent( Seq( "label1" -> parseFormula( "(exists x (p(x) & q(x)))")), Seq( "label2" -> parseFormula("(all y (p(y) -> (q(y) | r(y))))") ) )
) {
	use(DecomposeTactic)
}

val destructLemma = new Lemma(
	Sequent(Nil, Seq( "label1" -> parseFormula("a | (b | c)"), "label2" -> parseFormula( "a & (b & c)")))
) {
	use(DestructTactic("label1"))
	use(DestructTactic("label2"))
}

val destructLemma2 = new Lemma(
	Sequent(Seq("noise1" -> parseFormula("P(x)")), Seq( "noise2" -> parseFormula("P(y)"), "label1" -> parseFormula("a | (b | c)"), "noise3" -> parseFormula("P(z)"), "label2" -> parseFormula( "a & (b & c)" )))
) {
	use(DestructTactic())
	use(DestructTactic())
}

