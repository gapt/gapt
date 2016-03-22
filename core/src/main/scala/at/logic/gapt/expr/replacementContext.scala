package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.hol.HOLPosition

/**
 * Created by sebastian on 3/21/16.
 */

object replacementContext {
  def apply( ty: Ty, exp: LambdaExpression, positions: Seq[LambdaPosition], terms: LambdaExpression* ): Abs = {
    val x = rename( Var( "x", ty ), freeVariables( exp ) ++ terms flatMap { freeVariables( _ ) } )

    Abs( x, positions.foldLeft( exp ) { ( acc, p ) => acc.replace( p, x ) } )
  }

  def apply( ty: Ty, exp: LambdaExpression, positions: Seq[HOLPosition], terms: LambdaExpression* )( implicit d: DummyImplicit ): Abs = apply( ty, exp, positions map { HOLPosition.toLambdaPosition( exp ) }, terms: _* )

  def abstractTerm( exp: LambdaExpression )( t: LambdaExpression ): Abs = {
    val x = rename( Var( "x", t.exptype ), freeVariables( exp ) )
    Abs( x, TermReplacement( exp, t, x ) )
  }
}