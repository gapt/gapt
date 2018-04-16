package gapt.expr.hol

import gapt.expr._
import gapt.proofs.HOLClause
import org.specs2.mutable._

class CNFTest extends Specification {
  "the computation of CNFp(f)" should {
    "be {|- Pa,Qa, Qa|-} for f = (Pa ∨ Qa) ∧ ¬Qa" in {
      val Pa = FOLAtom( "P", FOLConst( "a" ) :: Nil )
      val Qa = FOLAtom( "Q", FOLConst( "a" ) :: Nil )
      val nQa = Neg( Qa )
      val PavQa = Or( Pa, Qa )
      val f = And( PavQa, nQa )
      CNFp( f ) must beEqualTo( Set( HOLClause( List(), List( Pa, Qa ) ), HOLClause( List( Qa ), List() ) ) )
    }
  }
}

