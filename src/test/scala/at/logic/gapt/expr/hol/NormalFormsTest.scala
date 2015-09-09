package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLClause
import org.specs2.mutable._

class CNFTest extends Specification {
  "the computation of CNFp(f)" should {
    "be {|- Pa,Qa, Qa|-} for f = (Pa ∨ Qa) ∧ ¬Qa" in {
      val Pa = FOLAtom( "P", FOLConst( "a" ) :: Nil )
      val Qa = FOLAtom( "Q", FOLConst( "a" ) :: Nil )
      val nQa = Neg( Qa )
      val PavQa = Or( Pa, Qa )
      val f = And( PavQa, nQa )
      CNFp.toClauseList( f ).toSet must beEqualTo( Set( HOLClause( List(), List( Pa, Qa ) ), HOLClause( List( Qa ), List() ) ) )
    }
  }
}

