import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val A = FOLAtom( "A" )
val B = FOLAtom( "B" )

val lemma = new Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	use( orR )
	use( negR )
	use( andR )
	use( repeat(axiom) )
	use( impL )
	use( repeat( axiom ) )
} qed

val lemma2 = new Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	use(repeat(orR orElse negR orElse andR orElse impL orElse axiom ))
} qed

val drinker3 = new Lemma( Sequent( Nil, Seq("E" -> parseFormula("B"), "E" -> parseFormula("A"), "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
	use(exR( parseTerm( "c" ), "D1" ))
	use(impR)
	use(allR)
	use(exR( parseTerm( "y" ), "D2" ))
	use(impR)
	use(allR)
	use(axiom)
} qed

val lemma3 = new Lemma( Sequent( Seq("F" -> parseFormula("A -> B")), Seq( "E" -> parseFormula("B"), "D" -> parseFormula( "(exists y (P(y) -> (all z P(z))))")))){
	use(impL)
	use(insert(drinker3))
	use(axiom)
} qed