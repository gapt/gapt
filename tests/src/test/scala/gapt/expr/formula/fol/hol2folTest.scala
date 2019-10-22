/*
 * hol2folTest.scala
 */

package gapt.expr.formula.fol

import gapt.expr._
import gapt.expr.formula
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Imp
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.hol.HOLFunction
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import org.specs2.mutable._

class hol2folTest extends Specification {
  def imap = Map[Expr, String]() // the scope for most tests is just the term itself
  def iid = new Counter

  "HOL terms" should {
    val hx = Var( "x", Ti ->: Ti )
    val ha = Const( "a", To ->: Ti )
    val hb = Const( "b", To ->: Ti )
    val fx = FOLVar( "x" )
    val fa = FOLConst( "a" )
    val fb = FOLConst( "b" )
    //TODO: fix the tests
    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        val hol = Atom( Const( "A", ( Ti ->: Ti ) ->: ( To ->: Ti ) ->: To ), hx :: ha :: Nil )
        val fol = FOLAtom( "A", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        val hol = HOLFunction( Const( "f", ( Ti ->: Ti ) ->: ( ( To ->: Ti ) ->: ( To ->: To ) ) ), hx :: ha :: Nil )
        val fol = FOLFunction( "f", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        val hA = Atom( Const( "A", ( Ti ->: Ti ) ->: ( ( To ->: Ti ) ->: To ) ), hx :: ha :: Nil )
        val hB = Atom( Const( "B", ( Ti ->: Ti ) ->: ( ( To ->: Ti ) ->: To ) ), hx :: hb :: Nil )
        val hol = And( hA, hB )
        val fA = FOLAtom( "A", fx :: fa :: Nil )
        val fB = formula.fol.FOLAtom( "B", fx :: fb :: Nil )
        val fol = And( fA, fB )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        val holf = le"f(λ(x:i>i) A(x, a:o>i)):o>o"
        val folf = fot"f('q_{1}')"
        reduceHolToFol( holf ) must beEqualTo( folf )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        val red = reduceHolToFol( le"f(λ(x:i>i) A(x, y:o>i)):o>o" )
        val fol = fot"f('q_{1}'(y))"
        red must beEqualTo( fol )
      }

      //TODO: check if this test case is really what we want
      "Two terms - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o) and g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" in {
        var id = iid // create new id function
        val ( f1, scope1 ) = reduceHolToFol( le"f(λ(x:i>i) A(x, y:o>i)):o>o", imap, id )
        val ( f2, scope2 ) = reduceHolToFol( le"g(λ(x:i>i) A(x, z:o>i)):o>o", scope1, id )

        List( f1, f2 ) must beEqualTo(
          List( fot"f('q_{1}'(y))", fot"g('q_{1}'(z))" ) )
      }

      "Correctly convert from type o to i on the termlevel" in {
        val List( sp, sq ) = List( "P", "Q" )
        val List( x, y ) = List( "x", "y" ).map( x => Atom( Var( x, To ), List() ) )
        val f1 = Atom( Const( sp, To ->: To ), List( Imp( x, y ) ) )
        val f2 = FOLAtom( sp, List( FOLFunction(
          ImpC.name,
          List(
            FOLVar( "x" ),
            FOLVar( "y" ) ) ) ) )

        val red = reduceHolToFol( f1 )
        red must beEqualTo( f2 )
      }
    }
  }

  "Type replacement" should {
    "work for simple terms" in {
      val folTerm: FOLTerm = fot"f q_1 c"
      val holTerm = changeTypeIn( folTerm, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      holTerm mustEqual le"(f : (i > i) > i > i) (q_1 : i > i) c"
    }
    "work for simple formulas" in {
      val folFormula: FOLFormula = fof"!x (P #v( q_1 : i) #c( q_1 : i ) )"
      val holFormula = changeTypeIn( folFormula, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      holFormula mustEqual hof"!x ((P : (i > i) > (i > i) > o) #v( q_1 : i > i) #c( q_1 : i > i) )"
    }
  }
}
