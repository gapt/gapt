package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.tape
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.proofs.{ Context, SequentMatchers }
import org.specs2.mutable.Specification

class makeTheoryAxiomsExplicitTest extends Specification with SequentMatchers {

  "tape" in {
    val ax =
      for {
        ( _, ( lhs, seq ) ) <- tape.ctx.get[Context.ProofNames].names
        if tape.ctx.get[Context.ProofDefinitions].find( lhs ).isEmpty
      } yield universalClosure( seq.toDisjunction )
    val withoutThAx = makeTheoryAxiomsExplicit( ax.toSeq: _* )( tape.proof )
    withoutThAx.subProofs.filter { _.isInstanceOf[ProofLink] } must_== Set()
    tape.ctx.check( withoutThAx )
    // TODO: multiset equality
    withoutThAx.conclusion must beSetEqual( ax ++: tape.proof.conclusion )
  }

}
