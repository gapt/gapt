import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

val A = FOLAtom( "A" )
val B = FOLAtom( "B" )

val lemma = Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	orR
	negR
	andR
	repeat(axiom)
	impL
	repeat(axiom)
}

val lemma2 = Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	repeat(orR orElse negR orElse andR orElse impL orElse axiom)
}

val drinker3 = Lemma( Sequent( Nil, Seq("E" -> parseFormula("B"), "E" -> parseFormula("A"), "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
	exR( parseTerm( "c" ) )
	impR
	allR
	exR( parseTerm( "y" ) )
	impR
	allR
	axiom
}

val lemma3 = Lemma( Sequent( Seq("F" -> parseFormula("A -> B")), Seq( "E" -> parseFormula("B"), "D" -> parseFormula( "(exists y (P(y) -> (all z P(z))))")))){
	impL
	insert(drinker3)
	axiom
}