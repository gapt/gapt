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
      val p0 = AndLeft1Rule( s1, term1oc, term2oc.formula.asInstanceOf[HOLFormula] )
      val p1 = AndLeft2Rule( p0, term1oc.formula.asInstanceOf[HOLFormula], p0.getDescendantInLowerSequent( term2oc ).get )
      ContractionLeftRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
    }

    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      val x1 = s1.root.antecedent.find( _.formula == term1 )
      if (x1 == None)
        throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      val x2 = s1.root.antecedent.find( x => x.formula == term2 && x != x1.get )
      if (x2 == None)
        throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      apply(s1, x1.get, x2.get)
    }
  }

  object OrRightRule {
    def apply(s1: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence) = {
      val p0 = OrRight1Rule( s1, term1oc, term2oc.formula )
      val p1 = OrRight2Rule( p0, term1oc.formula, p0.getDescendantInLowerSequent( term2oc ).get )
      ContractionRightRule( p1, p1.prin.head, p1.getDescendantInLowerSequent( p0.prin.head ).get )
    }

    // convenient method to choose the first formula
    def apply(s1: LKProof, term1: HOLFormula, term2: HOLFormula): UnaryTree[Sequent] with UnaryLKProof with AuxiliaryFormulas with PrincipalFormulas = {
      val x1 = s1.root.succedent.find( _.formula == term1 )
      if (x1 == None)
        throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      val x2 = s1.root.succedent.find( x => x.formula == term2 && x != x1.get )
      if (x2 == None)
        throw new LKRuleCreationException("Not matching formula occurrences found for application of the rule with the given formula")
      apply(s1, x1.get, x2.get)
    }
  }
}
