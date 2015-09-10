package at.logic.gapt.proofs.ralNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, Suc, Sequent }
import RalProof.Label

import org.specs2.mutable._

class RalProofTest extends Specification {

  implicit def expr2formula( expr: LambdaExpression ): HOLFormula = expr.asInstanceOf[HOLFormula]
  implicit def lexpr2lformula[T <: LambdaExpression]( lexpr: ( Set[T], LambdaExpression ) ): ( Label, HOLFormula ) =
    lexpr._1.asInstanceOf[Label] -> lexpr._2

  // Daniel's PhD thesis, p. 110
  "simple example" in {
    val f = Const( "f", Ti -> Ti )
    val X0 = Var( "X0", Ti -> To )
    val Y0 = Var( "Y0", Ti -> To )
    val x = Var( "x", Ti )
    val x0 = Var( "x0", Ti )
    val g = Const( "g", ( Ti -> To ) -> Ti )
    val T = Abs( X0, Abs( x, X0( x ) --> X0( f( x ) ) ) )

    val p1 = RalInitial( Sequent() :+ ( Set( Y0, T ) -> All( x, Y0( x ) --> Y0( f( x ) ) ) ) )
    val p2 = RalAllT( p1, Suc( 0 ), x0 )
    val p3 = RalImpT( p2, Suc( 0 ) )
    val p4 = RalSub( p3, Substitution( x0 -> g( Y0 ) ) )
    val p5 = RalInitial( Sequent() :+ ( Set( Y0 ) -> Y0( g( Y0 ) ) ) )
    val p6 = RalCut( p5, Seq( Suc( 0 ) ), p4, Seq( Ant( 0 ) ) )
    val p7 = RalSub( p3, Substitution( x0 -> f( g( Y0 ) ) ) )
    val p8 = RalCut( p6, Seq( Suc( 0 ) ), p7, Seq( Ant( 0 ) ) )
    val p9 = RalInitial( ( Set( Y0 ) -> Y0( f( f( g( Y0 ) ) ) ) ) +: Sequent() )
    val p10 = RalCut( p8, Seq( Suc( 0 ) ), p9, Seq( Ant( 0 ) ) )
    p10.conclusion.isEmpty must_== true
  }

}
