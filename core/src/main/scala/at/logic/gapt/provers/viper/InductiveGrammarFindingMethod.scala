package at.logic.gapt.provers.viper

import at.logic.gapt.expr.LambdaExpression
import at.logic.gapt.grammars.RecursionScheme

trait InductiveGrammarFindingMethod {
  def find( taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): RecursionScheme
}
