import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val A = FOLAtom( "A" )
val B = FOLAtom( "B" )

val someLemma = new Lemma(
	Sequent( Seq( "label1" -> parseFormula( "(exists x (p(x) & q(x)))")), Seq( "label2" -> parseFormula("(all y (p(y) -> (q(y) | r(y))))") ) )
) {
	use(DecomposeTactic)
}