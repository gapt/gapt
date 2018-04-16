package gapt.expr

import gapt.expr.hol.HOLPosition

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
   * @return
   */
  def apply( ty: Ty, exp: Expr, positions: Iterable[LambdaPosition] ): Abs = {
    val x = rename( Var( "x", ty ), containedNames( exp ) )
    Abs( x, positions.foldLeft( exp ) { ( acc, p ) => acc.replace( p, x ) } )
  }

  /**
   * Given an expression φ, creates an expression λx.φ', where φ' results from replacing some terms in φ with x.
   * The name of the variable x is automatically chosen to be fresh.
   * @param ty The type of x.
   * @param exp The expression φ.
   * @param positions The list of positions in φ to be replaced with x.
   * @return
   */
  def apply( ty: Ty, exp: Expr, positions: Iterable[HOLPosition] )( implicit d: DummyImplicit ): Abs =
    apply( ty, exp, positions map { HOLPosition.toLambdaPosition( exp ) } )

  /**
   * Transforms the expression φ to λx.φ' by replacing all occurrences of t in φ with x.
   * @param exp The expression φ.
   * @param t The term t.
   * @return
   */
  def abstractTerm( exp: Expr )( t: Expr ): Abs =
    apply( t.ty, exp, exp.find( t ) )
}