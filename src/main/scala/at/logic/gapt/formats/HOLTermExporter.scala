/*
 * HOLExpressionExporter.scala
 *
 */

package at.logic.gapt.formats

import at.logic.gapt.language.hol.HOLExpression

trait HOLTermExporter {
  def exportTerm( t: HOLExpression ): Unit
  def exportFunction( t: HOLExpression ): Unit // so arithmetical symbols can be parsed separately
}
