/*
 * hol2folTest.scala
 */

package at.logic.gapt.language.fol.algorithms

import at.logic.gapt.formats.simple.{ SimpleHOLParser, SimpleFOLParser }
import at.logic.gapt.language.fol
import at.logic.gapt.language.fol._
import at.logic.gapt.language.hol.logicSymbols.ImpSymbol
import at.logic.gapt.language.hol.{ HOLConst, HOLExpression, HOLVar, HOLAnd, HOLAtom, HOLFunction, HOLImp }
import at.logic.gapt.language.lambda.symbols.StringSymbol
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.formats.readers.StringReader
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class hol2folTest extends SpecificationWithJUnit {
  def imap = Map[HOLExpression, StringSymbol]() // the scope for most tests is just the term itself
  def iid = new { var idd = 0; def nextId = { idd = idd + 1; idd } }

  private class MyParserHOL( input: String ) extends StringReader( input ) with SimpleHOLParser
  private class MyParserFOL( input: String ) extends StringReader( input ) with SimpleFOLParser

  "HOL terms" should {
    val hx = HOLVar( "x", Ti -> Ti )
    val ha = HOLConst( "a", To -> Ti )
    val hb = HOLConst( "b", To -> Ti )
    val fx = FOLVar( "x" )
    val fa = FOLConst( "a" )
    val fb = FOLConst( "b" )
    //TODO: fix the tests
    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        val hol = HOLAtom( HOLConst( "A", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: ha :: Nil )
        val fol = FOLAtom( "A", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
        convertHolToFol( new MyParserHOL( "A(x:i, a:i)" ).getTerm() ) must beEqualTo( new MyParserFOL( "A(x, a)" ).getTerm() )
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        val hol = HOLFunction( HOLConst( "f", ( Ti -> Ti ) -> ( ( To -> Ti ) -> ( To -> To ) ) ), hx :: ha :: Nil )
        val fol = FOLFunction( "f", fx :: fa :: Nil )
        reduceHolToFol( hol ) must beEqualTo( fol )
        convertHolToFol.convertTerm( new MyParserHOL( "f(x:i, a:i):i" ).getTerm() ) must beEqualTo( new MyParserFOL( "f(x, a)" ).getTerm() )
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        val hA = HOLAtom( HOLConst( "A", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: ha :: Nil )
        val hB = HOLAtom( HOLConst( "B", ( Ti -> Ti ) -> ( ( To -> Ti ) -> To ) ), hx :: hb :: Nil )
        val hol = HOLAnd( hA, hB )
        val fA = FOLAtom( "A", fx :: fa :: Nil )
        val fB = FOLAtom( "B", fx :: fb :: Nil )
        val fol = FOLAnd( fA, fB )
        reduceHolToFol( hol ) must beEqualTo( fol )
        convertHolToFol( new MyParserHOL( "And A(x:i, a:i) B(x:i, b:i)" ).getTerm() ) must beEqualTo( new MyParserFOL( "And A(x, a) B(x, b)" ).getTerm() )
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
          List( new MyParserFOL( "f(q_{1}(y))" ).getTerm(), new MyParserFOL( "g(q_{1}(z))" ).getTerm() ) )
      }

      "Correctly convert from type o to i on the termlevel" in {
        val List( sp, sq ) = List( "P", "Q" )
        val List( x, y ) = List( "x", "y" ).map( x => HOLAtom( HOLVar( x, To ), List() ) )
        val f1 = HOLAtom( HOLConst( sp, To -> To ), List( HOLImp( x, y ) ) )
        val f2 = fol.FOLAtom( sp, List( fol.FOLFunction( ImpSymbol.toString,
          List( fol.FOLVar( "x" ),
            fol.FOLVar( "y" ) ) ) ) )

        val red = reduceHolToFol( f1 )
        red must beEqualTo( f2 )
      }
    }
  }

  "Type replacement" should {
    "work for simple terms" in {
      skipped( "TODO: fix this!" )
      val fterm1 = fol.FOLFunction( "f", List(
        fol.FOLConst( "q_1" ),
        fol.FOLConst( "c" ) ) )

      val fterm2 = fol.FOLAllVar( fol.FOLVar( "x" ),
        fol.FOLAtom( "P",
          List( fol.FOLVar( "q_1" ),
            fol.FOLConst( "q_1" ) ) ) )

      val hterm1 = changeTypeIn( fol2hol( fterm1 ), Map[String, TA]( ( "q_1", Ti -> Ti ) ) )
      val hterm2 = changeTypeIn( fol2hol( fterm2 ), Map[String, TA]( ( "q_1", Ti -> Ti ) ) )
      ok
    }
  }
}
