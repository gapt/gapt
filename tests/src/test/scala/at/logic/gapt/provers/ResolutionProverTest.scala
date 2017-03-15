package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class ResolutionProverTest extends Specification {

  "strong quantifiers and free variables" in {
    implicit var ctx = Context()
    ctx += TBase( "i" )
    ctx += hoc"'+': i>i>i"
    val formula = hof"!x!y x+y=y+x -> !x x+y=y+x"

    "lk" in {
      Escargot.getLKProof( formula ) must beLike {
        case Some( lk ) =>
          ctx.check( lk )
          lk.conclusion must_== hos":- $formula"
      }
    }

    "expansion" in {
      Escargot.getExpansionProof( formula ) must beLike {
        case Some( exp ) =>
          ctx.check( exp )
          exp.shallow must_== hos":- $formula"
      }
    }
  }

}
