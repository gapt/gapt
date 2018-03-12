package gapt.proofs.lk

import gapt.examples.tape
import gapt.expr._
import gapt.expr.hol.universalClosure
import gapt.proofs.{ Context, SequentMatchers }
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
