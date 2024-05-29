package gapt.examples

import gapt.examples.prime.furstenbergWitness
import org.specs2.mutable._
import org.specs2.specification.core.Fragments

class PrimeTest extends Specification {

  "prime proof" in {
    Fragments.foreach(0 to 5) { i =>
      s"n = $i" in {
        val primeI = prime.furstenberg(i)
        primeI.ctx.check(primeI.proof)
        ok
      }
    }
  }

  "furstenberg witness" in {
    Fragments.foreach(0 to 5) { i =>
      s"n = $i" in {
        furstenbergWitness(i)
        ok
      }
    }
  }

  "euclid proof" in {
    Fragments.foreach(0 to 5) { i =>
      s"n = $i" in {
        val euclidI = prime.euclid(i)
        euclidI.ctx.check(euclidI.proof)
        ok
      }
    }
  }

}
