package at.logic.gapt.expr

import at.logic.gapt.expr.hol.HOLPosition

/**
 * Creates a lambda expression that designates positions to be replaced.
 */
object replacementContext {

  /**
   * Given an expression φ, creates an expression λx.φ', where φ' results from replacing some terms in φ with x.
   * The name of the variable x is automatically chosen to be fresh.
   * @param ty The type of x.
   * @param exp The expression φ.
   * @param positions The list of positions in φ to be replaced with x.
   * @param terms Optional additional terms whose free variables are not valid choices for x.
   * @return
   */
  def apply( ty: Ty, exp: LambdaExpression, positions: Seq[LambdaPosition], terms: LambdaExpression* ): Abs = {
    val x = rename( Var( "x", ty ), freeVariables( exp ) ++ terms flatMap { freeVariables( _ ) } )

    Abs( x, positions.foldLeft( exp ) { ( acc, p ) => acc.replace( p, x ) } )
  }

  /**
   * Given an expression φ, creates an expression λx.φ', where φ' results from replacing some terms in φ with x.
   * The name of the variable x is automatically chosen to be fresh.
   * @param ty The type of x.
   * @param exp The expression φ.
   * @param positions The list of positions in φ to be replaced with x.
   * @param terms Optional additional terms whose free variables are not valid choices for x.
   * @return
   */
  def apply( ty: Ty, exp: LambdaExpression, positions: Seq[HOLPosition], terms: LambdaExpression* )( implicit d: DummyImplicit ): Abs = apply( ty, exp, positions map { HOLPosition.toLambdaPosition( exp ) }, terms: _* )

  /**
   * Transforms the expression φ to λx.φ' by replacing all occurrences of t in φ with x.
   * @param exp The expression φ.
   * @param t The term t.
   * @return
   */
  def abstractTerm( exp: LambdaExpression )( t: LambdaExpression ): Abs = {
    val pos = exp.find( t )
    apply( t.exptype, exp, pos, t )
  }
}