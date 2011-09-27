/*
 * ExpressionIdentities.scala
 *
 * This file supply traits and convenience classes to wrap LambdaExpressions with some ID so they can be easily retrieved from sequents.
 */

package at.logic.calculi

import at.logic.language.hol._

/**
 * The user can use abstract occurrences that mark different formulas or use positions as occurrences
 */
object occurrences {

import at.logic.utils.traits.Occurrence
import collection.immutable.Seq
import scala.Some

trait HasAncestors {
    val ancestors: Seq[Occurrence]
  }

  class FormulaOccurrence(val formula: HOLFormula,  override val ancestors: Seq[FormulaOccurrence], val factory : FOFactory) extends Occurrence with HasAncestors
  implicit def focc2f(fo: FormulaOccurrence): Formula = fo.formula

  trait FOFactory {
    def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence
  }

  object defaultFormulaOccurrenceFactory extends FOFactory {
    def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence = 
    new FormulaOccurrence(formula, ancestors, this)
  }
  
  implicit val factory = defaultFormulaOccurrenceFactory

}
