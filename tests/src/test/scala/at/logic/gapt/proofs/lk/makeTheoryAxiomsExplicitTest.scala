package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.tape
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class makeTheoryAxiomsExplicitTest extends Specification with SequentMatchers {

  "tape" in {
    val ax = tape.ctx.axioms.map( a => univclosure( a.toDisjunction ) )
    val withoutThAx = makeTheoryAxiomsExplicit( ax: _* )( tape.p )
    withoutThAx.subProofs.filter { _.isInstanceOf[TheoryAxiom] } must_== Set()
    tape.ctx.check( withoutThAx )
    // TODO: multiset equality
    withoutThAx.conclusion must beSetEqual( ax ++: tape.p.conclusion )
  }

}
