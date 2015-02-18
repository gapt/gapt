/*
 * Wrapper function for beta-reduction in Schema.
 *
 **/

package at.logic.gapt.language.schema

import at.logic.gapt.language.lambda.{ BetaReduction => BetaReductionLambda }
import at.logic.gapt.language.lambda.BetaReduction.ImplicitStandardStrategy._

object BetaReduction {

  def betaNormalize( expression: SchemaExpression ): SchemaExpression =
    BetaReductionLambda.betaNormalize( expression ).asInstanceOf[SchemaExpression]

  def betaReduce( expression: SchemaExpression ): SchemaExpression =
    BetaReductionLambda.betaReduce( expression ).asInstanceOf[SchemaExpression]
}
