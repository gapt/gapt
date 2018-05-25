/*
 * Tests for verit's interface.
**/

package gapt.provers.smtlib

import gapt.examples.BussTautology
import gapt.expr._
import gapt.proofs.HOLSequent
import org.specs2.mutable._

class SmtInterpolTest extends Specification {

  "SmtInterpol" should {
    "prove a ∨ ¬ a" in {
      val a = FOLAtom( "a" )
      SmtInterpol.isValid( Or( a, Neg( a ) ) ) must_== true
    }

    "a |- a" in {
      val a = FOLAtom( "a" )
      SmtInterpol.isValid( a +: HOLSequent() :+ a ) must_== true
    }

    "prove top" in {
      SmtInterpol.isValid( HOLSequent() :+ Top() ) must_== true
    }

    "not prove bottom" in {
      SmtInterpol.isValid( HOLSequent() :+ Bottom() ) must_== false
    }

    "not refute top" in {
      SmtInterpol.isValid( Top() +: HOLSequent() ) must_== false
    }

    "refute bottom" in {
      SmtInterpol.isValid( Bottom() +: HOLSequent() ) must_== true
    }

    "validate the buss tautology for n=1" in {
      SmtInterpol.isValid( BussTautology( 1 ) ) must_== true
    }
  }
}
