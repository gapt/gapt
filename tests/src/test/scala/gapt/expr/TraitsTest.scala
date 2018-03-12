package gapt.expr

import org.specs2.mutable._

class TraitsTest extends Specification {
  "Top and Bottom" should {
    "have PropFormula" in {
      Bottom() must beAnInstanceOf[PropFormula]
      Top() must beAnInstanceOf[PropFormula]
    }
  }

  "And, Or, Imp" should {
    "preserve Formula" in {
      val f = App( Abs( FOLVar( "x" ), Bottom() ), FOLConst( "c" ) )
      f must beAnInstanceOf[Formula]
      And( f, f ) must beAnInstanceOf[Formula]
      Or( f, f ) must beAnInstanceOf[Formula]
      Imp( f, f ) must beAnInstanceOf[Formula]
    }

    "preserve FOLFormula" in {
      val f = All( FOLVar( "x" ), FOLAtom( "R", FOLVar( "x" ) ) )
      And( f, f ) must beAnInstanceOf[FOLFormula]
      Or( f, f ) must beAnInstanceOf[FOLFormula]
      Imp( f, f ) must beAnInstanceOf[FOLFormula]
    }

    "preserve PropFormula" in {
      val f = FOLAtom( "R" )
      And( f, f ) must beAnInstanceOf[PropFormula]
      Or( f, f ) must beAnInstanceOf[PropFormula]
      Imp( f, f ) must beAnInstanceOf[PropFormula]
    }
  }

  "atoms" in {
    val x = FOLVar( "x" )
    Eq( x, x ) must beAnInstanceOf[FOLAtom]
  }

  "FOL terms" should {
    val f = Const( "f", FOLHeadType( Ti, 1 ) )

    "be closed under functions" in {
      App( f, FOLConst( "c" ) ) must beAnInstanceOf[FOLTerm]
    }

    "not contain lambda abstractions" in {
      App( f, App( Abs( FOLVar( "x" ), FOLVar( "x" ) ), FOLVar( "x" ) ) ) must not be anInstanceOf[FOLExpression]
    }
  }

  "LogicalConstant" should {
    "be on quantifiers" in {
      ForallC( Ti ) must beAnInstanceOf[LogicalConstant]
      ForallC( Ti ->: Ti ) must beAnInstanceOf[LogicalConstant]
      ExistsC( Ti ->: Ti ) must beAnInstanceOf[LogicalConstant]
    }
  }
}
