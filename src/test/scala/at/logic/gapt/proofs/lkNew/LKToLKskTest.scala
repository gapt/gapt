package at.logic.gapt.proofs.lkNew

import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr.{ All, FOLVar, FOLAtom }
import at.logic.gapt.provers.prover9.Prover9Prover

import org.specs2.mutable._

class LKToLKskTest extends Specification {
  "single strong quantifier inference" in {
    val f = FOLAtom( "p", FOLVar( "x" ) )
    val qf = All( FOLVar( "x" ), f )

    val p1 = LogicalAxiom( f )
    val p2 = ForallLeftRule( p1, qf )
    val p3 = ForallRightRule( p2, qf )

    val pSk = LKToLKsk( p3 )
    pSk.conclusion must_== ( p3.endSequent map { Seq() -> _ } )
  }

  "pigeonhole" in {
    if ( !new Prover9Prover().isInstalled ) skipped

    LKToLKsk( Pi2Pigeonhole() )
    ok
  }
}
