import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics._

val p = new Lemma( Sequent(
  Seq( "L" -> parseFormula( "(all x all y (P(x,y) -> Q(x,y)))" )),
  Seq( "R" -> parseFormula( "(exists x exists y (-Q(x,y) -> -P(x,y)))" )))) {

  use(CutTactic( parseFormula( "(all x exists y (-P(x,y) | Q(x,y)))" ), "C" ))

  // left subproof
  use(WeakeningRightTactic( "R" ))
  use(ForallRightTactic( FOLVar( "z" ), "C" ))
  use(ExistsRightTactic( parseTerm( "a" ), "C1" ))
  use(ForallLeftTactic( parseTerm( "z" ), "L1" ))
  use(ForallLeftTactic( parseTerm( "a" ), "L2", "L1" ))
  use(OrRightTactic( "C1" ))
  use(ImpLeftTactic( "L2" ))
  use(NegRightTactic( "C1_1" ))
  use(LogicalAxiomTactic( parseFormula( "P(z,a)" )))
  use(LogicalAxiomTactic( parseFormula( "Q(z,a)" )))

  // right subproof
  use(WeakeningLeftTactic( "L" ))
  use(ForallLeftTactic( parseTerm( "b" ), "C1" ))
  use(ExistsLeftTactic( FOLVar( "v" ), "C1" ))
  use(ExistsRightTactic( parseTerm( "b" ), "R1" ))
  use(ExistsRightTactic( parseTerm( "v" ), "R2" ))
  use(WeakeningLeftTactic( "C" ))
  use(WeakeningRightTactic( "R" ))
  use(WeakeningRightTactic( "R1" ))
  use(ImpRightTactic( "R2" ))
  use(NegRightTactic( "R2_2" ))
  use(NegLeftTactic( "R2_1" ))
  use(OrLeftTactic( "C1" ))
  use(NegLeftTactic( "C1" ))
  use(LogicalAxiomTactic( parseFormula( "P(b,v)" )))
  use(LogicalAxiomTactic( parseFormula( "Q(b,v)" )))
} qed

