/*
 * HOLExpressionExporter.scala
 *
 */

package at.logic.parsing.language

import at.logic.language.hol.HOLExpression

trait HOLTermExporter {
  def exportTerm(t: HOLExpression): Unit
  def exportFunction(t: HOLExpression): Unit // so arithmetical symbols can be parsed separately
}
