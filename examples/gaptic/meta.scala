import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val A = FOLAtom( "A" )
val B = FOLAtom( "B" )

val lemma = new Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	use( OrRightTactic( ) )
	use( NegRightTactic( ) )
	use( AndRightTactic( ) )
	use( RepeatTactic( AxiomTactic ) )
	use( ImpLeftTactic( ) )
	use( RepeatTactic( AxiomTactic ) )
} qed

val lemma2 = new Lemma(
	Sequent( Seq( "A" -> Imp( A, B ) ), Seq( "S" -> Or( And( A, B ), Neg( A ) ) ) )
) {
	use(RepeatTactic(OrRightTactic( ) orElse NegRightTactic( ) orElse AndRightTactic( ) orElse ImpLeftTactic( ) orElse AxiomTactic ))
} qed