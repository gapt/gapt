package gapt.expr

import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Top
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.LogicalConstant
import gapt.expr.formula.constants.OrC
import gapt.expr.formula.constants.TopC
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFormulaWithBoundVar
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLHeadType
import gapt.expr.formula.fol.FOLPartialAtom
import gapt.expr.formula.fol.FOLPartialFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.ty.->:
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.variables
import gapt.proofs.Sequent
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
      R must beAnInstanceOf[FOLPartialAtom]
      R.asInstanceOf[FOLPartialAtom].numberOfArguments must be_==( 2 )

      App( R, c ) must beAnInstanceOf[FOLPartialAtom]
      Apps( R, c, c ) must beAnInstanceOf[FOLFormula]

      Abs( x, Apps( R, x, x ) ) must beAnInstanceOf[FOLFormulaWithBoundVar]
      App( ForallC( Ti ), Abs( x, Apps( R, x, x ) ) ) must beAnInstanceOf[FOLFormula]

      AndC() must beAnInstanceOf[FOLPartialFormula]
      Apps( AndC(), Apps( R, c, c ), Apps( R, c, c ) ) must beAnInstanceOf[FOLFormula]

      TopC() must beAnInstanceOf[FOLFormula]
      TopC() must beAnInstanceOf[LogicalConstant]
    }
  }

  "N-ary connectives" should {
    "match correctly" in {
      val p = FOLAtom( "p" )
      val q = FOLAtom( "q" )
      val r = FOLAtom( "r" )
      val Fl = And( p, And( q, r ) )
      val Fr = And( And( p, q ), r )

      Fl must beLike { case And.nAry( Seq( `p`, `q`, `r` ) ) => ok }
      Fr must beLike { case And.nAry( Seq( `p`, `q`, `r` ) ) => ok }
    }
  }

  "Apps" should {
    "match applications in the correct order" in {
      FOLFunction( "f", List( "a", "b", "c" ).map( FOLConst( _ ) ) ) must beLike {
        case Apps( Const( "f", Ti ->: Ti ->: Ti ->: Ti, Nil ), List( FOLConst( "a" ), FOLConst( "b" ), FOLConst( "c" ) ) ) => ok
      }
    }
  }

  "FOL helpers" should {
    "have correct static types" in {
      And( FOLAtom( "R" ), FOLAtom( "P" ) ) must beAnInstanceOf[FOLFormula]
      All( FOLVar( "x" ), FOLAtom( "R", FOLVar( "x" ) ) ) must beAnInstanceOf[FOLFormula]
      Top() must beAnInstanceOf[FOLFormula]
      ok
    }
  }

  "toString" should {
    "terminate" in {
      FOLAtom( "P" ).toString must beEqualTo( "P:o" )
    }
  }

  "variables and free variables" should {
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val M1 = App( Abs( x, Abs( y, x ) ), x )

    val u = FOLVar( "u" )
    val v = FOLVar( "v" )
    val t1 = FOLFunction( "f", FOLFunction( "g", u ), v )

    "be extracted correctly from " + M1 in {
      variables( M1 ) must beEqualTo( Set( x, y ) )
      freeVariables( M1 ) must beEqualTo( Set( x ) )
    }

    "be extracted correctly from the FOLTerm " + t1 in {
      variables( t1 ) must beEqualTo( Set( u, v ) )
      freeVariables( t1 ) must beEqualTo( Set( u, v ) )
    }
  }

  "constants" should {
    "all" should {
      "return all the occurring constants" in {
        constants.all( hof"#c(A : o) & #v( B: o) | #v(x : i) = x | ! x #v( X : i > o)(x)" ) must_==
          Set( OrC(), AndC(), ForallC( Ti ), EqC( Ti ), hoc"A : o" )
      }
    }
    "equalities" should {
      "return all equality constants and only equality constants" in {
        constants.equalities( le"#v(x : i) = #c(y :i) & #c(f: i > i) = #v(g: i > i)" ) must_==
          Set( EqC( Ti ), EqC( Ti ->: Ti ) )
      }
    }
    "return all non-logical constants in iterable" in {
      val es = Seq( le"#c(P : i > o)( #v(x : i) )", le"&", le"#c( c : i )" )
      constants.nonLogical( es ) must_== Set( hoc"P : i > o", hoc"c : i" )
    }
    "return all non-logical constants in sequent" in {
      val s = Sequent( Seq( hof"#c(P : i > o)( #v(x : i) )", le"|" ), Seq( hof"#c(A : o) & ! x #v( B : i > o )(x)" ) )
      constants.nonLogical( s ) must_== Set( hoc"P : i > o", hoc"A : o" )
    }
    "constants" in {
      "non-logical" should {
        "not return logic constants" in {
          val x = Var( "x", To )
          constants.nonLogical( Ex( x, All( x, ( x | x === x | Top() | Bottom() ) --> ( x & -x ) ) ) ) must_== Set()
        }
      }
    }
  }
}
