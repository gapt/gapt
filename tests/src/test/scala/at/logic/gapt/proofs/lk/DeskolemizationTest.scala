package at.logic.gapt.proofs.lk
import at.logic.gapt.examples.CountingEquivalence
import at.logic.gapt.expr._
import at.logic.gapt.proofs.SequentMatchers
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class DeskolemizationTest extends Specification with SequentMatchers {

  "drinker" in {
    val Some( drinker ) = Escargot.getLKProof( hof"?x (p(x) -> !y p(y))" )
    val deskolemized = deskolemizeLK( drinker )
    deskolemized.endSequent must beSetEqual( drinker.endSequent )
  }

  "counting" in {
    val Some( proof ) = Escargot.getLKProof( CountingEquivalence( 0 ) )
    val deskolemized = deskolemizeLK( proof )
    deskolemized.endSequent must beSetEqual( proof.endSequent )
  }

  "quantifier shifting" in {
    val Some( proof ) = Escargot.getLKProof( hof"!x?y!z?w P(x,y,z,w) -> !x!z?y?w P(x,y,z,w)" )
    val deskolemized = deskolemizeLK( proof )
    deskolemized.endSequent must beSetEqual( proof.endSequent )
  }

}
