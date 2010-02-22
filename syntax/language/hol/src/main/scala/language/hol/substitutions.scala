/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import scala.collection.immutable._
import at.logic.language.lambda.substitutions.{Substitution => LambdaSubstitution}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression,Var}
import at.logic.language.hol._


package substitutions {
  class Substitution protected[substitutions](m: scala.collection.immutable.Map[HOLVar, HOLExpression]) extends LambdaSubstitution(m.asInstanceOf[Map[Var,LambdaExpression]]) {
    def apply( formula: Formula ) : Formula = apply( formula.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
    // cannot call this method "apply" because of signature clash with other method due to erasure :-(
    def applyHOL( term: HOLExpression ) : HOLExpression = apply( term ).asInstanceOf[HOLExpression]
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[HOLVar, HOLExpression]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[HOLVar, HOLExpression]() ++ subs)
    def apply(subs: Tuple2[HOLVar, HOLExpression]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[HOLVar, HOLExpression]]): Substitution = apply(subs.elements)
    def apply(variable: HOLVar, expression: HOLExpression): Substitution = apply((variable, expression))
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)
  }
}
