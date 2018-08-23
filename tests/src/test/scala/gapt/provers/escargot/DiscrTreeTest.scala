package gapt.provers.escargot

import gapt.examples.Pi2Pigeonhole
import gapt.examples.theories.{ nat, natdivisible }
import gapt.expr.{ Expr, syntacticMGU, syntacticMatching }
import gapt.expr.fol.folSubTerms
import gapt.proofs.lk.LKToExpansionProof
import gapt.provers.escargot.impl.DiscrTree
import org.specs2.mutable.Specification

class DiscrTreeTest extends Specification {

  "test 1" in {
    val terms =
      folSubTerms(
        LKToExpansionProof( Pi2Pigeonhole.proof ).
          deep.toFormula )
    var tree = DiscrTree[Expr]()
    for ( t <- terms ) tree = tree.insert( t, t )
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMatching( _, t1 ).isDefined )
      val actual = tree.generalizations( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMGU( _, t1 ).isDefined )
      val actual = tree.unifiable( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    ok
  }

  "test 2" in {
    val terms =
      folSubTerms(
        LKToExpansionProof( nat.mulcomm.combined() ).
          deep.toFormula )
    var tree = DiscrTree[Expr]()
    for ( t <- terms ) tree = tree.insert( t, t )
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMatching( _, t1 ).isDefined )
      val actual = tree.generalizations( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMGU( _, t1 ).isDefined )
      val actual = tree.unifiable( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    ok
  }

}
