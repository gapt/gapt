package at.logic.gapt.examples

import org.specs2.mutable._
import org.specs2.specification.core.Fragments

class PrimeTest extends Specification {

  "prime proof" in {
    Fragments.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        val primeI = prime.prime( i )
        primeI.ctx.check( primeI.proof )
        ok
      }
    }
  }

  "euclid proof" in {
    Fragments.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        val euclidI = prime.euclid( i )
        euclidI.ctx.check( euclidI.proof )
        ok
      }
    }
  }

}
