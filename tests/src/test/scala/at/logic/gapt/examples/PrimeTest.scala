package at.logic.gapt.examples

import at.logic.gapt.provers.smtlib.Z3
import org.specs2.mutable._
import org.specs2.specification.core.Fragments

class PrimeTest extends Specification {

  "prime proof" in {
    Fragments.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        skipped( "z3 times out on theory axioms" )
        if ( !Z3.isInstalled ) skipped
        prime.prime( i ).proof
        ok
      }
    }
  }

}
