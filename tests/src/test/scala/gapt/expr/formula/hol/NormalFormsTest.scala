package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.{ And, Formula, Neg, Or }
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.logic.hol.{ CNFp, simplify }
import gapt.proofs.HOLClause
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

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

class SimplifyTest extends Specification {
  "simplify" should {
    def succeedFor(inputFormula: Formula, expectedSimplifiedFormula: Formula): Fragment = {
      s"""map "$inputFormula" to "$expectedSimplifiedFormula"""" in {
        simplify(inputFormula) must beEqualTo(expectedSimplifiedFormula)
      }
    }

    succeedFor(hof"(P ∨ Q) ∧ P", hof"P")
    succeedFor(hof"c=c", hof"⊤")
    succeedFor(hof"c!=c", hof"⊥")
    succeedFor(hof"P ∧ P ∧ P", hof"P")
    succeedFor(hof"!x (x=t -> P(x))", hof"P(t)")
    succeedFor(hof"P -> ¬P", hof"¬P")
    succeedFor(hof"¬(¬P)", hof"P")
  }
}

