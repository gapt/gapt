/*
 * LambdaExpressionExporter.scala
 *
 */

package at.logic.gapt.formats

import at.logic.gapt.expr.LambdaExpression

trait HOLTermExporter {
  def exportTerm( t: LambdaExpression ): Unit
  def exportFunction( t: LambdaExpression ): Unit // so arithmetical symbols can be parsed separately
}
