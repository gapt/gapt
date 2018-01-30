package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ Notation, Precedence }
import at.logic.gapt.proofs.MutableContext
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class ResolutionProverTest extends Specification {
  sequential

  "strong quantifiers and free variables" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += TBase( "i" )
    ctx += hoc"'+': i>i>i"
    ctx += Notation.Infix( "+", Precedence.plusMinus )
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
