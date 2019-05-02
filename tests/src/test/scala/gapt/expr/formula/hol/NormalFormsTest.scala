package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.logic.hol.CNFp
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

