/*
 * HOLExpressionExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language

import at.logic.language.lambda.typedLambdaCalculus._

trait HOLTermExporter {
  def exportTerm(t: LambdaExpression): Unit
  def exportFunction(t: LambdaExpression): Unit // so arithmetical symbols can be parsed separately
}
