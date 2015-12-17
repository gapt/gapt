import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val drinker = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x all y (P(x) -> P(y)))" )))) {
  use(ExistsRightTactic( parseTerm( "c" ), "D1" ))
  use(ForallRightTactic( FOLVar( "y_0" ), "D1" ))
  use(ExistsRightTactic( parseTerm( "y_0" ), "D2" ))
  use(ForallRightTactic( FOLVar( "y_1" ), "D2" ))
  use(ImpRightTactic( "D1" ))
  use(ImpRightTactic( "D2" ))
  use(LogicalAxiomTactic( parseFormula( "P(y_0)" )))
} qed

