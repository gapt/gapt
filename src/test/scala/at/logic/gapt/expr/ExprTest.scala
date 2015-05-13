package at.logic.gapt.expr

import at.logic.gapt.expr.{ To, Ti }
import org.specs2.mutable._

class ExprTest extends Specification {
  "FOL traits for expressions constructed by hand" should {
    val f = Const( "f", FOLHeadType( Ti, 3 ) )
    val c = Const( "c", Ti )
    val R = Const( "R", FOLHeadType( To, 2 ) )
    val x = Var( "x", Ti )

    "be on terms" in {
      Apps( f, c, c, c ) must beAnInstanceOf[FOLTerm]

      x must beAnInstanceOf[FOLVar]
    }

    "be on formulas" in {
      R must beAnInstanceOf[FOLLambdaTerm]
      R.asInstanceOf[FOLLambdaTerm].numberOfArguments must be_==( 2 )

      App( R, c ) must beAnInstanceOf[FOLLambdaTerm]
      Apps( R, c, c ) must beAnInstanceOf[FOLFormula]

      Abs( x, Apps( R, x, x ) ) must beAnInstanceOf[FOLFormulaWithBoundVar]
      App( ForallC( Ti ), Abs( x, Apps( R, x, x ) ) ) must beAnInstanceOf[FOLFormula]

      AndC() must beAnInstanceOf[FOLLambdaTerm]
      Apps( AndC(), Apps( R, c, c ), Apps( R, c, c ) ) must beAnInstanceOf[FOLFormula]

      TopC() must beAnInstanceOf[FOLFormula]
      TopC() must beAnInstanceOf[LogicalConstant]
    }
  }

  "FOL helpers" should {
    "have correct static types" in {
      val a: FOLTerm = FOLFunction( "f", FOLVar( "x" ), FOLFunction( "c" ) )
      val b: FOLFormula = FOLAtom( "R", FOLVar( "x" ), FOLFunction( "c" ) )
      val c: FOLFormula = And( FOLAtom( "R" ), FOLAtom( "P" ) )
      val d: FOLFormula = All( FOLVar( "x" ), FOLAtom( "R", FOLVar( "x" ) ) )
      val e: FOLFormula = Top()
      ok
    }
  }

  "toString" should {
    "terminate" in {
      FOLAtom( "P" ).toString must beEqualTo( "P" )
    }
  }
}
