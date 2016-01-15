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

val drinker3 = new Lemma( Sequent( Nil, Seq("E" -> parseFormula("B"), "E" -> parseFormula("A"), "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
	use(ExistsRightTactic( parseTerm( "c" ), "D1" ))
	use(ImpRightTactic())
	use(ForallRightTactic())
	use(ExistsRightTactic( parseTerm( "y" ), "D2" ))
	use(ImpRightTactic())
	use(ForallRightTactic())
	use(AxiomTactic)
} qed

val lemma3 = new Lemma( Sequent( Seq("F" -> parseFormula("A -> B")), Seq( "E" -> parseFormula("B"), "D" -> parseFormula( "(exists y (P(y) -> (all z P(z))))")))){
	use(ImpLeftTactic())
	use(InsertTactic(drinker3))
	use(AxiomTactic)
} qed