package at.logic.gapt.examples

import org.specs2.mutable._
import org.specs2.specification.core.Fragments

class PrimeTest extends Specification {

  "prime proof" in {
    Fragments.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        prime.prime( i ).proof
        ok
      }
    }
  }

  "euclid proof" in {
    Fragments.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        prime.euclid( i ).proof
        ok
      }
    }
  }

}
