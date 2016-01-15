/*
 * SimpleFOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.expr.simple

import at.logic.gapt.formats.simple.SimpleFOLParser
import org.specs2.mutable._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._
import at.logic.gapt.formats.readers.StringReader

class SimpleFOLParserTest extends Specification {
  private class MyParser( input: String ) extends StringReader( input ) with SimpleFOLParser

  val var1 = FOLVar( "x1" )
  val const1 = FOLConst( "c1" )
  val var2 = FOLVar( "x2" )
  val atom1 = FOLAtom( "A", var1 :: var2 :: const1 :: Nil )
  val var3 = FOLAtom( "X3", Nil )
  val func1 = FOLFunction( "f", var1 :: var2 :: const1 :: Nil )
  val and1 = And( atom1, var3 )
  val or1 = Or( atom1, var3 )
  val imp1 = Imp( atom1, var3 )
  val neg1 = Neg( atom1 )
  val ex1 = Ex( var1, atom1 )
  val all1 = All( var1, atom1 )
  val npx = Neg( FOLAtom( "p", FOLVar( "x" ) :: Nil ) )

  "SimpleFOLParser" should {
    "parse correctly a variable" in {
      ( new MyParser( "x1" ).getTerm() ) must beEqualTo( var1 )
    }
    "parse correctly an constant" in {
      ( new MyParser( "c1" ).getTerm() ) must beEqualTo( const1 )
    }
    "parse correctly an atom" in {
      ( new MyParser( "A(x1, x2, c1)" ).getTerm() ) must beEqualTo( atom1 )
    }
    "parse correctly a formula" in {
      ( new MyParser( "X3" ).getTerm() ) must beLike { case x: FOLFormula => ok }
      ( new MyParser( "X3" ).getTerm() ) must beEqualTo( var3 )
    }
    "parse correctly a function 1" in {
      ( new MyParser( "f(x1)" ).getTerm() ) must beEqualTo( FOLFunction( "f", var1 :: Nil ) )
    }
    "parse correctly a function 2" in {
      ( new MyParser( "f(x1, x2, c1)" ).getTerm() ) must beEqualTo( func1 )
    }
    "parse correctly an and" in {
      ( new MyParser( "And A(x1, x2, c1) X3" ).getTerm() ) must beEqualTo( and1 )
    }
    "parse correctly an or" in {
      ( new MyParser( "Or A(x1, x2, c1) X3" ).getTerm() ) must beEqualTo( or1 )
    }
    "parse correctly an imp" in {
      ( new MyParser( "Imp A(x1, x2, c1) X3" ).getTerm() ) must beEqualTo( imp1 )
    }
    "parse correctly an neg" in {
      ( new MyParser( "Neg A(x1, x2, c1)" ).getTerm() ) must beEqualTo( neg1 )
    }
    "parse correctly an exists" in {
      ( new MyParser( "Exists x1 A(x1, x2, c1)" ).getTerm() ) must beEqualTo( ex1 )
    }
    "parse correctly a forall" in {
      ( new MyParser( "Forall x1 A(x1, x2, c1)" ).getTerm() ) must beEqualTo( all1 )
    }
    "reject the empty string" in {
      ( new MyParser( "" ).getTerm() ) must throwAn[Exception]
    }
    "reject the string p(X)" in {
      ( new MyParser( "p(X)" ).getTerm() ) must throwAn[Exception]
    }
  }
}
