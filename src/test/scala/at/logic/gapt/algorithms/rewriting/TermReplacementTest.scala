package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.proofs.{ Ant, Suc, Clause }
import org.specs2.mutable._
import at.logic.gapt.expr.fol._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.expr._

/**
 * Test for replacment of constant symbols by terms
 */
class TermReplacementTest extends Specification {

  val c1 = FOLAtom( "P", FOLFunction( "g", FOLConst( "a" ) :: Nil ) :: Nil )
  val c2 = FOLAtom( "P", FOLFunction( "g", FOLVar( "x" ) :: Nil ) :: Nil )
  val c3 = FOLAtom( "Q", FOLFunction( "f", FOLConst( "ladr0" ) :: Nil ) :: Nil )
  val c4 = FOLAtom( "Q", FOLVar( "x" ) :: Nil )

  val x = FOLVar( "x" )
  val a = FOLConst( "a" )
  val fl = FOLFunction( "f", FOLConst( "ladr0" ) :: Nil )

  val d1 = FOLAtom( "R", FOLFunction( "f", FOLConst( "a" ) :: Nil ) :: Nil )
  val d2 = FOLAtom( "R", FOLFunction( "f", FOLVar( "x" ) :: Nil ) :: Nil )
  val d3 = FOLAtom( "Q", FOLFunction( "h", FOLConst( "c0" ) :: Nil ) :: Nil )
  val d4 = FOLAtom( "Q", FOLVar( "x" ) :: Nil )

  val hc = FOLFunction( "h", FOLConst( "c0" ) :: Nil )

  object proof1 {
    val p1 = InputClause( c1 +: c1 +: Clause() :+ c3 )
    val p2 = InputClause( Clause() :+ c2 )
    val p3 = InputClause( c4 +: Clause() )
    val p5 = MguResolution( p2, Suc( 0 ), p1, Ant( 1 ) )
    val p6 = MguResolution( p5, Suc( 0 ), p3, Ant( 0 ) )
    val p7 = MguResolution( p2, Suc( 0 ), p6, Ant( 0 ) )
  }

  object proof2 {
    val q1 = InputClause( d1 +: d1 +: Clause() :+ d3 )
    val q2 = InputClause( Clause() :+ d2 )
    val q3 = InputClause( d4 +: Clause() )
    val q5 = MguResolution( q2, Suc( 0 ), q1, Ant( 1 ) )
    val q6 = MguResolution( q5, Suc( 0 ), q3, Ant( 0 ) )
    val q7 = MguResolution( q2, Suc( 0 ), q6, Ant( 0 ) )
  }

  object proof3 {
    val p0 = InputClause( c1 +: c2 +: Clause() :+ c3 )
    val p1 = Factor( p0, Ant( 0 ), Ant( 1 ) )
    val p2 = InputClause( Clause() :+ c2 )
    val p3 = InputClause( c4 +: Clause() )
    val p5 = MguResolution( p2, Suc( 0 ), p1, Ant( 0 ) )
    val p6 = MguResolution( p5, Suc( 0 ), p3, Ant( 0 ) )
  }

  object proof4 {
    val q0 = InputClause( d1 +: d2 +: Clause() :+ d3 )
    val q1 = MguFactor( q0, Ant( 0 ), Ant( 1 ) )
    val q2 = InputClause( Clause() :+ d2 )
    val q3 = InputClause( d4 +: Clause() )
    val q5 = MguResolution( q2, Suc( 0 ), q1, Ant( 0 ) )
    val q6 = MguResolution( q5, Suc( 0 ), q3, Ant( 0 ) )

  }

  "Term replacement " should {
    " work on lambda terms " in {

      val termx = FOLFunction( "term", FOLVar( "x" ) :: Nil )
      val terma = FOLFunction( "term", FOLConst( "a" ) :: Nil )
      val hihix = FOLFunction( "hihi", FOLVar( "x" ) :: Nil )

      val o1 = FOLFunction( "g", FOLFunction( "f", FOLFunction( "g", FOLConst( "f" ) :: Nil ) :: FOLConst( "c" ) :: Nil ) :: FOLFunction( "f", FOLVar( "x" ) :: FOLConst( "f" ) :: Nil ) :: Nil )
      val o2 = FOLFunction( "term", termx :: terma :: terma :: termx :: Nil )

      val r1 = FOLFunction( "g", FOLFunction( "f", FOLFunction( "g", FOLVar( "x" ) :: Nil ) :: FOLConst( "c" ) :: Nil ) :: FOLFunction( "f", FOLVar( "x" ) :: FOLVar( "x" ) :: Nil ) :: Nil )
      val r2 = FOLFunction( "term", hihix :: terma :: terma :: hihix :: Nil )

      val t1 = FOLConst( "f" )
      val t2 = FOLVar( "x" )
      val t3 = FOLFunction( "term", FOLVar( "x" ) :: Nil )
      val t4 = FOLFunction( "hihi", FOLVar( "x" ) :: Nil )

      val rt1 = TermReplacement( o1, t1, t2 )
      val rt2 = TermReplacement( o2, t3, t4 )
      rt1 must be_==( r1 )
      rt2 must be_==( r2 )

      val map = Map[FOLExpression, FOLExpression]( ( t1 -> t2 ), ( t3 -> t4 ) )
      rt1 must be_==( TermReplacement( o1, map ) )
      rt2 must be_==( TermReplacement( o2, map ) )
    }

    " work on simple proofs " in {

      val t1 = FOLFunction( "replacement", FOLVar( "x0" ) :: FOLVar( "y0" ) :: Nil )
      val t2 = FOLFunction( "really", FOLVar( "x1" ) :: Nil )

      val map = Map[LambdaExpression, LambdaExpression]( a -> t1, hc -> t2 )

      val initial = TermReplacement( proof4.q0, map )

      val r1 = FOLAtom( "R", FOLFunction( "f", t1 :: Nil ) :: Nil )
      val r2 = FOLAtom( "R", FOLFunction( "f", FOLVar( "x" ) :: Nil ) :: Nil )
      val r3 = FOLAtom( "Q", t2 :: Nil )

      initial.conclusion must_== ( r1 +: r2 +: Clause() :+ r3 )

      val more = TermReplacement( proof4.q6, map )

      ok
    }
  }
}
