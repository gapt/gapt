/*
 * Tests for verit's interface.
**/

package at.logic.gapt.provers.z3

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.smtlib.Z3
import org.specs2.mutable._

class Z3ProverTest extends Specification {

  args( skipAll = !Z3.isInstalled )

  "z3" should {
    "prove a v not a" in {
      val a = FOLAtom( "a" )
      Z3.isValid( Or( a, Neg( a ) ) ) must_== true
    }

    "a |- a" in {
      val a = FOLAtom( "a" )
      Z3.isValid( a +: HOLSequent() :+ a ) must_== true
    }

    "prove top" in {
      Z3.isValid( HOLSequent() :+ Top() ) must_== true
    }

    "not prove bottom" in {
      Z3.isValid( HOLSequent() :+ Bottom() ) must_== false
    }

    "not refute top" in {
      Z3.isValid( Top() +: HOLSequent() ) must_== false
    }

    "refute bottom" in {
      Z3.isValid( Bottom() +: HOLSequent() ) must_== true
    }

    "validate the buss tautology for n=1" in {
      Z3.isValid( BussTautology( 1 ) ) must_== true
    }
  }
}
