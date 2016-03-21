package at.logic.gapt.grammars

import at.logic.gapt.expr._

import org.specs2.mutable.Specification

class AntiUnificationTest extends Specification {
  "antiUnifier" should {
    "compute au of first-order terms" in {
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val au = antiUnifier( FOLFunction( "f", c, c ), FOLFunction( "f", d, d ) )._1
      val x = FOLVar( "x" )
      Abs( freeVariables( au ).toSeq, au ) must_== Abs( x, FOLFunction( "f", x, x ) )
    }
    "compute au of many-sorted terms" in {
      val data = TBase( "Data" )
      val tree = TBase( "Tree" )
      val node = Const( "Node", data -> ( tree -> ( tree -> tree ) ) )

      val a = Const( "a", data )
      val t = Const( "t", tree )
      val s = Const( "s", tree )

      val au = antiUnifier( node( a, t, t ), node( a, s, s ) )._1

      val x = Var( "x", tree )
      Abs( freeVariables( au ).toSeq, au ) must_== Abs( x, node( a, x, x ) )
    }

    "terms with free variables" in {
      val a = le"f(x1, c)"
      val b = le"f(x1, d)"
      val ( au, s1, s2 ) = antiUnifier( a, b )
      Substitution( s1 )( au ) must_== a
      Substitution( s2 )( au ) must_== b
    }
  }

  "antiUnifier1" should {
    "terms with free variables" in {
      val a = le"f(x, c)"
      val b = le"f(x, d)"
      val ( au, s1, s2 ) = antiUnifier1( a, b )
      Substitution( s1 )( au ) must_== a
      Substitution( s2 )( au ) must_== b
    }
  }
}
