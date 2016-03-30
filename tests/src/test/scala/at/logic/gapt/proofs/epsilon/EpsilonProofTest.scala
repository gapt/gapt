package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class EpsilonProofTest extends Specification with SatMatchers {

  "linear example" in {
    val p = EpsilonProof(
      Seq( le"c", le"f c", le"f (f c)", le"f (f (f c))" ) map {
        CriticalFormula( hof"∃x ¬(P x ⊃ P (f x))", _ )
      },
      hof"P c" +: hof"∀x (P x ⊃ P (f x))" +: Sequent() :+ hof"P (f (f (f (f c))))"
    )
    p.deep must beValidSequent
  }

  "quantifier blocks" in {
    Escargot getEpsilonProof hof"∀x∀y∀z P(x,y,z) ⊃ ∃x∃y∃z P(f x, g y, h z)" must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

  "deskolemization" in {
    Escargot getEpsilonProof hof"∀x∃y∀z P(x,y,z) ⊃ ∃z∀x∃y P(x,y,z)" must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

}
