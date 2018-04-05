package gapt.proofs.lk

import gapt.examples.{ nTape3, primediv }
import gapt.proofs.{ MutableContext, SequentMatchers }
import org.specs2.mutable.Specification

class SkolemizeInferencesTest extends Specification with SequentMatchers {

  "primediv" in {
    val p = primediv.proof
    implicit val ctx: MutableContext = primediv.ctx.newMutable
    skolemizeLK( p ).endSequent must beMultiSetEqual( p.endSequent )
    skolemizeLK( p, proofTheoretic = false ).endSequent must beMultiSetEqual( p.endSequent )
  }

  "ntape3" in {
    val p = nTape3.input_proof
    implicit val ctx: MutableContext = MutableContext.guess( p )
    skolemizeLK( p ).endSequent must beMultiSetEqual( p.endSequent )
    skolemizeLK( p, proofTheoretic = false ).endSequent must beMultiSetEqual( p.endSequent )
  }

}
