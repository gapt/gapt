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

  class FormulaOccurrence(val formula: Formula,  override val ancestors: Seq[FormulaOccurrence]) extends Occurrence with HasAncestors
  implicit def focc2f(fo: FormulaOccurrence): Formula = fo.formula
  object FormulaOccurrence {
    def apply(f: Formula, ancestors: Seq[FormulaOccurrence]) = new FormulaOccurrence(f, ancestors)
    def unapply(fo: FormulaOccurrence) = Some(fo.formula, fo.ancestors)
  }
}