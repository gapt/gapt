package gapt.expr.util

import gapt.expr.Abs
import gapt.expr.Expr
import gapt.expr.ReplacementContext
import gapt.expr.Ty
import gapt.expr.Var
import gapt.expr.containedNames
import gapt.expr.hol.HOLPosition

/**
 * Creates capture avoiding replacement contexts.
 */
object replacementContext {

  /**
   * Creates a replacement context.
   *
   * @param ty The type of the holes.
   * @param exp An expression φ for which a context is to be created.
   * @param positions A list of non-overlapping positions p_1, ..., p_n in φ.
   * @return An expression of the form λx.φ', where x is a fresh variable of
   * type `ty` and φ' = φ[p_1/x, ..., p_n/x].
   */
  def apply( ty: Ty, exp: Expr, positions: Iterable[LambdaPosition] ): ReplacementContext = {
    val x = rename( Var( "x", ty ), containedNames( exp ) )
    Abs( x, positions.foldLeft( exp ) { ( acc, p ) => acc.replace( p, x ) } )
  }

  /**
   * Creates a replacement context.
   *
   * @param ty The type of the holes.
   * @param exp An expression φ for which a context is to be created.
   * @param positions A list of non-overlapping positions p_1, ..., p_n in φ.
   * @return See `replacementContext.apply()`.
   */
  def apply( ty: Ty, exp: Expr, positions: Iterable[HOLPosition] )( implicit d: DummyImplicit ): ReplacementContext =
    apply( ty, exp, positions map { HOLPosition.toLambdaPosition( exp ) } )

  /**
   * Creates a replacement context.
   *
   * @param exp The expression φ for which a context is to be created.
   * @param t The term t to be replaced by holes.
   * @return An expression of the form λx.φ', where x is a fresh variable and
   * φ' = φ[t/x].
   */
  def abstractTerm( exp: Expr )( t: Expr ): ReplacementContext =
    apply( t.ty, exp, exp.find( t ) )
}
