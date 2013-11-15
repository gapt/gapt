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
import scala.Some

trait HasAncestors {
  val ancestors: Seq[Occurrence]
}

class FormulaOccurrence(val formula: HOLFormula,  override val ancestors: Seq[FormulaOccurrence], val factory : FOFactory) extends Occurrence with HasAncestors {
  val id = defaultFormulaOccurrenceFactory.freshId()   //makes it easier to detect problems with identic formulas/ancestors but different object ids
  override def toString = formula.toString + "[" + id + "]"
  
  override def clone() : java.lang.Object = {
    println("Cloning ID: "+id)
    super.clone()
  }
  // returns true if o is an ancestor of the current occurrence
  def isAncestor(o: FormulaOccurrence): Boolean =
    if (this == o) true
    else ancestors.exists(_.isAncestor(o))
}
implicit def focc2f(fo: FormulaOccurrence): Formula = fo.formula

//FO = FormulaOccurrence
trait FOFactory {
  def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence
}

object defaultFormulaOccurrenceFactory extends FOFactory {
  def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence = 
  new FormulaOccurrence(formula, ancestors, this)

  private var id_counter = 10000
  def freshId() = { id_counter = id_counter +1; id_counter }
}

implicit val factory = defaultFormulaOccurrenceFactory

}

