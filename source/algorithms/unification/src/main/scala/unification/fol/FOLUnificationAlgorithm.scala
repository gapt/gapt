/*
 * FOLUnificationAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.unification.fol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.unification.UnificationAlgorithm
import at.logic.language.fol._

object FOLUnificationAlgorithm extends UnificationAlgorithm {
  def unifiy(term1: LambdaExpression, term2: LambdaExpression) = {
    require(term1.isInstanceOf[FOL] && term2.isInstanceOf[FOL])
    //Some(Substitution())
    None
  }

}
