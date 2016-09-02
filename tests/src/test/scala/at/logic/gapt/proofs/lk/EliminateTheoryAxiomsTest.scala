package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.tape
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.SequentMatchers
import org.specs2.mutable.Specification

class EliminateTheoryAxiomsTest extends Specification with SequentMatchers {

  "tape" in {
    val ax = univclosure( And( tape.ctx.axioms.map( _.toDisjunction ) ) )
    val withoutThAx = eliminateTheoryAxioms( tape.p, ax )
    withoutThAx.subProofs.filter { _.isInstanceOf[TheoryAxiom] } must_== Set()
    // TODO: multiset equality
    withoutThAx.conclusion must beSetEqual( ax +: tape.p.conclusion )
  }

}
