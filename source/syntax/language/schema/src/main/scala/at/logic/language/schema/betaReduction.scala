/*
 * Wrapper function for beta-reduction in Schema.
 *
 **/

package at.logic.language.schema

import at.logic.language.lambda.{BetaReduction => BetaReductionLambda}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._

object BetaReduction {

  def betaNormalize(expression: SchemaExpression) : SchemaExpression = 
    BetaReductionLambda.betaNormalize(expression).asInstanceOf[SchemaExpression]

  def betaReduce(expression: SchemaExpression) : SchemaExpression = 
    BetaReductionLambda.betaReduce(expression).asInstanceOf[SchemaExpression]
}
