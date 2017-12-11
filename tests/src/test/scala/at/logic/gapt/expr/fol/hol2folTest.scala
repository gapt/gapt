/*
 * hol2folTest.scala
 */

package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
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
        val fB = FOLAtom( "B", fx :: fb :: Nil )
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
      skipped( "TODO: fix this!" )
      val fterm1 = FOLFunction( "f", List(
        FOLConst( "q_1" ),
        FOLConst( "c" ) ) )

      val fterm2 = All(
        FOLVar( "x" ),
        FOLAtom(
          "P",
          List(
            FOLVar( "q_1" ),
            FOLConst( "q_1" ) ) ) )

      val hterm1 = changeTypeIn( fterm1, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      val hterm2 = changeTypeIn( fterm2, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      ok
    }
  }
}
