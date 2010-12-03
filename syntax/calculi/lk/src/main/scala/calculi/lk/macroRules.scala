/*
 * macroRules.scala
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._
import lkExtractors._
import propositionalRules._

package macroRules {
  object AndLeftRule {
    def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
      val p0 = AndLeft1Rule( s1, term1oc, term2oc.formula )
      val p1 = AndLeft2Rule( p0, term1oc.formula, p0.getDescendantInLowerSequent( term2oc ).get )
      ContractionLeftRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
    }

    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[SequentOccurrence] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      s1.root.antecedent.filter(x => x.formula == term1).toList.zip(s1.root.antecedent.filter(x => x.formula == term2)) match {
        case ((x1,x2)::_) => apply(s1, x1, x2)
        case _ => throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      }
    }
  }
}
