/*
 * Wrapper function for beta-reduction in HOL.
 *
 **/

package at.logic.gapt.language.hol

import at.logic.gapt.expr.BetaReduction.ImplicitStandardStrategy._
import at.logic.gapt.expr.{ BetaReduction => BetaReductionLambda }

object BetaReduction {

  def betaNormalize( expression: HOLExpression ): HOLExpression =
    BetaReductionLambda.betaNormalize( expression ).asInstanceOf[HOLExpression]

  def betaNormalize( expression: HOLFormula ): HOLFormula =
    BetaReductionLambda.betaNormalize( expression ).asInstanceOf[HOLFormula]

  def betaReduce( expression: HOLExpression ): HOLExpression =
    BetaReductionLambda.betaReduce( expression ).asInstanceOf[HOLExpression]

  def betaReduce( expression: HOLFormula ): HOLFormula =
    BetaReductionLambda.betaReduce( expression ).asInstanceOf[HOLFormula]
}
