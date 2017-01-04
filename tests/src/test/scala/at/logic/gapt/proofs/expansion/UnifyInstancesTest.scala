package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import org.specs2.mutable.Specification

class UnifyInstancesTest extends Specification {

  "example" in {
    val lk = Lemma( ( "hyp" -> hof"!x!y (p(x) & q(y))" ) +:
      Sequent()
      :+ ( "conj" -> hof"q(c) & p(c)" ) ) {

      destruct( "conj" )
      // two instance vectors:
      allL( le"x", le"c" ); prop
      allL( le"c", le"y" ); prop
    }

    val exp = LKToExpansionProof( lk )
    numberOfInstancesET( exp ) must_== 4

    val unified = unifyInstancesET( exp )
    // now just one instance vector:
    numberOfInstancesET( unified ) must_== 2
  }

}
