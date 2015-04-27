/*
 * Wrapper function for beta-reduction in FOL.
 *
 **/

package at.logic.gapt.language.fol

import at.logic.gapt.expr.{ BetaReduction => BetaReductionLambda }
import at.logic.gapt.expr.BetaReduction.ImplicitStandardStrategy._

object BetaReduction {

  def betaNormalize( expression: FOLExpression ): FOLExpression =
    BetaReductionLambda.betaNormalize( expression ).asInstanceOf[FOLExpression]

  def betaNormalize( expression: FOLFormula ): FOLFormula =
    BetaReductionLambda.betaNormalize( expression ).asInstanceOf[FOLFormula]

  def betaReduce( expression: FOLExpression ): FOLExpression =
    BetaReductionLambda.betaReduce( expression ).asInstanceOf[FOLExpression]
}
