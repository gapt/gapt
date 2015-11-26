/*
 * hol2folTest.scala
 */

package at.logic.gapt.expr.fol

import at.logic.gapt.formats.simple.{ SimpleHOLParser, SimpleFOLParser }
import at.logic.gapt.expr._
import at.logic.gapt.formats.readers.StringReader
import org.specs2.mutable._

class hol2folTest extends Specification {
  def imap = Map[LambdaExpression, StringSymbol]() // the scope for most tests is just the term itself
  def iid = new { var idd = 0; def nextId = { idd = idd + 1; idd } }

  private class MyParserHOL( input: String ) extends StringReader( input ) with SimpleHOLParser
  private class MyParserFOL( input: String ) extends StringReader( input ) with SimpleFOLParser

  "HOL terms" should {
    val hx = Var( "x", Ti -> Ti )
    val ha = Const( "a", To -> Ti )
    val hb = Const( "b", To -> Ti )
    val fx = FOLVar( "x" )
    val fa = FOLConst( "a" )
    val fb = FOLConst( "b" )
    //TODO: fix the tests
    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        val hol = HOLAtom( Const( "A", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: ha :: Nil )
        val fol = FOLAtom( "A", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        val hol = HOLFunction( Const( "f", ( Ti -> Ti ) -> ( ( To -> Ti ) -> ( To -> To ) ) ), hx :: ha :: Nil )
        val fol = FOLFunction( "f", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        val hA = HOLAtom( Const( "A", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: ha :: Nil )
        val hB = HOLAtom( Const( "B", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: hb :: Nil )
        val hol = And( hA, hB )
        val fA = FOLAtom( "A", fx :: fa :: Nil )
        val fB = FOLAtom( "B", fx :: fb :: Nil )
        val fol = And( fA, fB )
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        val holf = new MyParserHOL( "f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" ).getTerm()
        val folf = new MyParserFOL( "f(q_{1})" ).getTerm()
        reduceHolToFol( holf ) must beEqualTo( folf )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        val red = reduceHolToFol( new MyParserHOL( "f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" ).getTerm() )
        val fol = ( new MyParserFOL( "f(q_{1}(y))" ).getTerm() )
        red must beEqualTo( fol )
      }

      //TODO: check if this test case is really what we want
      "Two terms - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o) and g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" in {
        var id = iid // create new id function
        val ( f1, scope1 ) = reduceHolToFol( new MyParserHOL( "f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" ).getTerm(), imap, id )
        val ( f2, scope2 ) = reduceHolToFol( new MyParserHOL( "g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" ).getTerm(), scope1, id )

        List( f1, f2 ) must beEqualTo(
          List( new MyParserFOL( "f(q_{1}(y))" ).getTerm(), new MyParserFOL( "g(q_{1}(z))" ).getTerm() )
        )
      }

      "Correctly convert from type o to i on the termlevel" in {
        val List( sp, sq ) = List( "P", "Q" )
        val List( x, y ) = List( "x", "y" ).map( x => HOLAtom( Var( x, To ), List() ) )
        val f1 = HOLAtom( Const( sp, To -> To ), List( Imp( x, y ) ) )
        val f2 = FOLAtom( sp, List( FOLFunction(
          ImpC.name,
          List(
            FOLVar( "x" ),
            FOLVar( "y" )
          )
        ) ) )

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
        FOLConst( "c" )
      ) )

      val fterm2 = All(
        FOLVar( "x" ),
        FOLAtom(
          "P",
          List(
            FOLVar( "q_1" ),
            FOLConst( "q_1" )
          )
        )
      )

      val hterm1 = changeTypeIn( fterm1, Map[String, Ty]( ( "q_1", Ti -> Ti ) ) )
      val hterm2 = changeTypeIn( fterm2, Map[String, Ty]( ( "q_1", Ti -> Ti ) ) )
      ok
    }
  }
}
