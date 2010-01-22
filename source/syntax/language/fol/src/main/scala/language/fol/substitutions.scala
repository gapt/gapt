
/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.fol

import scala.collection.immutable._
import at.logic.language.hol.substitutions.{Substitution => HOLSubstitution}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression,Var}
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._


package substitutions {
  class Substitution protected[substitutions](m: scala.collection.immutable.Map[FOLVar, FOLExpression]) extends HOLSubstitution(m.asInstanceOf[Map[HOLVar,HOLTerm]]) {
    // cannot call this method "apply" because of signature clash with other method due to erasure :-(
    def applyFOL( term: FOLExpression ) : FOLExpression = apply( term ).asInstanceOf[FOLExpression]
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[FOLVar, FOLExpression]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[FOLVar, FOLExpression]() ++ subs)
    def apply(subs: Tuple2[FOLVar, FOLExpression]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[FOLVar, FOLExpression]]): Substitution = apply(subs.elements)
    def apply(variable: FOLVar, expression: FOLExpression): Substitution = apply((variable, expression))
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)

  }
}