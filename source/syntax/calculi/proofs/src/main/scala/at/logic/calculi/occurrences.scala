package at.logic.calculi

import at.logic.language.hol._

package occurrences {

  /**
   * A formula occurrence is an occurrence of a [[HOLFormula]] in a proof.  Both formulas in different sequents and
   * multiple occurrences of the same formula (e.g. introduced by contraction) have a different [[FormulaOccurrence]].
   *
   * @param formula  The formula of which this is an occurrence.
   * @param ancestors  What occurrences caused this occurrence, i.e. if this occurrence is introduced by or-right, then
   *                   this will include the disjunction is occurrence.
   * @param factory  The formula occurrence factory [[FOFactory]] used to construct this occurrence.
   */
  class FormulaOccurrence(val formula: HOLFormula, val ancestors: Seq[FormulaOccurrence], val factory : FOFactory) {
    /**
     * Auto-incremented integer identifying this occurrence.
     */
    val id = defaultFormulaOccurrenceFactory.freshId()

    override def toString = s"$formula[$id]"

    override def clone() : java.lang.Object = {
      println("Cloning ID: "+id)
      super.clone()
    }

    /**
     * Recursively checks whether the argument is an ancestor of this occurrence.
     */
    def isAncestor(o: FormulaOccurrence): Boolean =
      if (this == o) true
      else ancestors.exists(_.isAncestor(o))
  }

//FO = FormulaOccurrence
  /**
   * Formula occurrence factory.  This factory is stored in [[FormulaOccurrence]] itself, sometimes passed via an
   * implicit {{{factory}}} parameter, or directly linked to [[defaultFormulaOccurrenceFactory]].
   *
   * Specialized factories can return instances of subclasses of [[FormulaOccurrence]],
   * e.g. [[at.logic.calculi.lksk.LKskFOFactory]].
   *
   * FIXME: The only supported factory is [[defaultFormulaOccurrenceFactory]] at the moment.
   */
trait FOFactory {
  def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence
}

  /**
   * Creates instances of [[FormulaOccurrence]].
   */
  object defaultFormulaOccurrenceFactory extends FOFactory {
    def createFormulaOccurrence(formula: HOLFormula, ancestors: Seq[FormulaOccurrence]): FormulaOccurrence =
      new FormulaOccurrence(formula, ancestors, this)

    private var id_counter = 10000
    private[occurrences] def freshId() = { id_counter = id_counter +1; id_counter }
  }

}

package object occurrences {
  implicit val factory = defaultFormulaOccurrenceFactory

  /**
   * Implicitly converts a [[FormulaOccurrence]] to the formula its occurrence it records.
   */
  implicit def formulaOccurrenceToFormula(fo: FormulaOccurrence): Formula = fo.formula
}

