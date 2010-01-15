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
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._


package substitutions {
  class Substitution protected[substitutions](m: scala.collection.immutable.Map[HOLVar, HOLTerm]) extends LambdaSubstitution(m.asInstanceOf[Map[Var,LambdaExpression]]) {
    def apply( formula: Formula ) : Formula = apply( formula.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
    // cannot call this method "apply" because of signature clash with other method due to erasure :-(
    def applyHOL( term: HOLTerm ) : HOLTerm = apply( term ).asInstanceOf[HOLTerm]
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[HOLVar, HOLTerm]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[HOLVar, HOLTerm]() ++ subs)
    def apply(subs: Tuple2[HOLVar, HOLTerm]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[HOLVar, HOLTerm]]): Substitution = apply(subs.elements)
    def apply(variable: HOLVar, expression: HOLTerm): Substitution = apply((variable, expression))
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)
  }
}
