
/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.fol

import scala.collection.immutable._
import at.logic.language.lambda.substitutions.{Substitution => LambdaSubstitution}
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression,Var}
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._


package substitutions {
  class Substitution protected[substitutions](m: scala.collection.immutable.Map[FOLVar, FOLTerm]) extends LambdaSubstitution(m.asInstanceOf[Map[Var,LambdaExpression]]) {
    def apply( formula: Formula ) : Formula = apply( formula.asInstanceOf[LambdaExpression] ).asInstanceOf[Formula]
    // cannot call this method "apply" because of signature clash with other method due to erasure :-(
    def applyFOL( term: FOLTerm ) : FOLTerm = apply( term ).asInstanceOf[FOLTerm]

    
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[FOLVar, FOLTerm]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[FOLVar, FOLTerm]() ++ subs)
    def apply(subs: Tuple2[FOLVar, FOLTerm]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[FOLVar, FOLTerm]]): Substitution = apply(subs.elements)
    def apply(variable: FOLVar, expression: FOLTerm): Substitution = apply((variable, expression))
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)

  }
}