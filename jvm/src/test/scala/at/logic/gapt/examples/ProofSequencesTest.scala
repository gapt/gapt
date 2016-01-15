package at.logic.gapt.examples

import org.specs2.mutable._
import org.specs2.specification.core.Fragments

class ProofSequencesTest extends Specification {

  "proof sequences" should {
    "produce proofs" in {
      Fragments.foreach( proofSequences ) { proofSequence =>
        proofSequence.name in {
          Fragments.foreach( 0 to 10 ) { i =>
            s"n = $i" in {
              proofSequence( i )
              ok
            }
          }
        }
      }
    }
  }

}
