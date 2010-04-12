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
import at.logic.language.hol._


package substitutions {
  class Substitution protected[substitutions](m: scala.collection.immutable.Map[FOLVar, FOLExpression]) extends HOLSubstitution(m.asInstanceOf[Map[HOLVar,HOLExpression]]) {
    // cannot call this method "apply" because of signature clash with other method due to erasure :-(
    def applyFOL( term: FOLExpression ) : FOLExpression = apply( term ).asInstanceOf[FOLExpression]
    //def applyFOL( subst: FOLExpression ) : FOLExpression = apply( term ).asInstanceOf[FOLExpression]
    def mapFOL() : scala.collection.immutable.Map[FOLVar, FOLExpression] = map.asInstanceOf[scala.collection.immutable.Map[FOLVar, FOLExpression]]

    //compose substitutions, i.e. apply substitution to other_subst before concatenating
    def composeFOL(other_subst : Substitution) : Substitution = {
      new Substitution(m ++ other_subst.mapFOL.map((x:Pair[FOLVar, FOLExpression]) => (x._1, applyFOL(x._2))))
    }

    //add a new variable mapping to the substitution 
    def concatFOL(other_subst : Substitution) : Substitution = {
      new Substitution(m ++ other_subst.mapFOL.elements)
    }

    /*
    override def :::( s :at.logic.language.lambda.substitutions.Substitution) : at.logic.language.lambda.substitutions.Substitution = {
      s match {
        case Substitution => concatFOL(s)
        case _ => super.:::(s)
      }
    }
    */
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[FOLVar, FOLExpression]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[FOLVar, FOLExpression]() ++ subs)
    def apply(subs: Tuple2[FOLVar, FOLExpression]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[FOLVar, FOLExpression]]): Substitution = apply(subs.elements)
    def apply(variable: FOLVar, expression: FOLExpression): Substitution = apply((variable, expression))
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)
  }
}