import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val drinker = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  use(ExistsRightTactic( parseTerm( "c" ), "D1" ))
  use(ImpRightTactic( "D1" ))
  use(ForallRightTactic( FOLVar( "y_0" ), "D1_2" ))
  use(ExistsRightTactic( parseTerm( "y_0" ), "D2" ))
  use(ImpRightTactic( "D2" ))
  use(ForallRightTactic( FOLVar( "y_1" ), "D2_2" ))
  use(LogicalAxiomTactic( parseFormula( "P(y_0)" )))
} qed

val dualdrinker = new Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))")), Nil )) {
  use(ForallLeftTactic( parseTerm( "c" ), "D1" ))
  use(AndLeftTactic( "D1" ))
  use(ExistsLeftTactic( FOLVar( "y_0" ) ))
  use(NegLeftTactic( "D1_2" ))
  use(ForallLeftTactic( parseTerm( "y_0" ), "D2" ))
  use(AndLeftTactic( "D2" ))
  use(ExistsLeftTactic( FOLVar( "y_1" ) ))
  use(NegLeftTactic( "D2_2" ))
  use(LogicalAxiomTactic( parseFormula( "P(y_0)" )))
} qed

