/*
 * SimpleHOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.expr.simple

import at.logic.gapt.formats.simple.SimpleHOLParser
import org.specs2.mutable._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.readers.StringReader

class SimpleHOLParserTest extends Specification {
  private class MyParser( input: String ) extends StringReader( input ) with SimpleHOLParser
  "SimpleHOLParser" should {
    val var1 = Var( ( "x1" ), Ti -> ( Ti -> Ti ) )
    "parse correctly a variable" in {
      ( new MyParser( "x1: (i -> (i -> i))" ).getTerm() ) must beEqualTo( var1 )
    }
    val const1 = Const( ( "c1" ), Ti -> Ti )
    "parse correctly an constant" in {
      ( new MyParser( "c1: (i -> i)" ).getTerm() ) must beEqualTo( const1 )
    }
    val var2 = Var( ( "x2" ), Ti )
    val atom1 = HOLAtom( Const( ( "a" ), var1.exptype -> ( var2.exptype -> ( const1.exptype -> To ) ) ), var1 :: var2 :: const1 :: Nil )
    "parse correctly an atom" in {
      ( new MyParser( "a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))" ).getTerm() ) must beEqualTo( atom1 )
    }
    "parse correctly an abs" in {
      ( new MyParser( "Abs x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))" ).getTerm() ) must beEqualTo( Abs( var1, atom1 ) )
    }
    val var3 = HOLAtom( Var( "x3", To ) )
    "parse correctly a formula variable" in {
      ( new MyParser( "x3: o" ).getTerm() ) must beLike { case x: HOLFormula => ok }
    }
    "parse correctly a formula constant" in {
      ( new MyParser( "c: o" ).getTerm() ) must beLike { case x: HOLFormula => ok }
    }
    val f1 = HOLFunction( Const( ( "f" ), Ti -> Ti ), Const( ( "a" ), Ti ) :: Nil )
    "parse correctly a function" in {
      ( new MyParser( "f(a:i):i" ) ).getTerm must beEqualTo( f1 )
    }
    val f2 = HOLFunction( Var( ( "x" ), Ti -> Ti ), Const( ( "a" ), Ti ) :: Nil )
    "parse correctly a function variable 1" in {
      val term = ( new MyParser( "x(a:i):i" ) ).getTerm
      term must beEqualTo( f2 )
    }
    val and1 = And( atom1, var3 )
    "parse correctly an and" in {
      ( new MyParser( "And a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o" ).getTerm() ) must beEqualTo( and1 )
    }
    val or1 = Or( atom1, var3 )
    "parse correctly an or" in {
      ( new MyParser( "Or a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o" ).getTerm() ) must beEqualTo( or1 )
    }
    val imp1 = Imp( atom1, var3 )
    "parse correctly an imp" in {
      ( new MyParser( "Imp a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o" ).getTerm() ) must beEqualTo( imp1 )
    }
    val neg1 = Neg( atom1 )
    "parse correctly an neg" in {
      ( new MyParser( "Neg a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))" ).getTerm() ) must beEqualTo( neg1 )
    }
    val ex1 = Ex( var1, atom1 )
    "parse correctly an exists" in {
      ( new MyParser( "Exists x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))" ).getTerm() ) must beEqualTo( ex1 )
    }
    val all1 = All( var1, atom1 )
    "parse correctly a forall" in {
      ( new MyParser( "Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))" ).getTerm() ) must beEqualTo( all1 )
    }
    val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
    "parse correctly a complex term" in {
      ( new MyParser( str ).getTerm() ) must not( throwAn[Exception] )
    }
  }

}
