package at.logic.gapt.proofs

import at.logic.gapt.expr._

package occurrences {

  import at.logic.gapt.expr.HOLFormula

  /**
   * A formula occurrence is an occurrence of a [[HOLFormula]] in a proof.  Both formulas in different sequents and
   * multiple occurrences of the same formula (e.g. introduced by contraction) have a different [[FormulaOccurrence]].
   *
   * @param formula  The formula of which this is an occurrence.
   * @param parents  What occurrences caused this occurrence, i.e. if this occurrence is introduced by or-right, then
   *                   this will include the disjunction is occurrence.
   * @param factory  The formula occurrence factory [[FOFactory]] used to construct this occurrence.
   */
  class FormulaOccurrence( val formula: HOLFormula, val parents: Seq[FormulaOccurrence], val factory: FOFactory ) {
    /**
     * Auto-incremented integer identifying this occurrence.
     */
    val id = defaultFormulaOccurrenceFactory.freshId()

    override def toString = s"$formula[$id]"

    override def clone(): java.lang.Object = {
      println( "Cloning ID: " + id )
      super.clone()
    }

    /**
     * Tests whether this is a descendant of that.
     *
     * @param that A formula occurrence.
     * @param reflexive Whether this should count as a descendant of itself.
     * @return
     */
    def isDescendantOf( that: FormulaOccurrence, reflexive: Boolean ): Boolean =
      if ( reflexive && this == that )
        true
      else if ( parents.contains( that ) )
        true
      else
        parents.exists( _.isDescendantOf( that, reflexive = false ) )

    /**
     * Tests whether this is an ancestor of that.
     *
     * @param that A formula occurrence.
     * @param reflexive Whether this should count as an ancestor of itself.
     * @return
     */
    def isAncestorOf( that: FormulaOccurrence, reflexive: Boolean ): Boolean = that.isDescendantOf( this, reflexive )

    /**
     *
     * @return The ancestors of this, i.e. its parents and the ancestors of its parents.
     */
    def ancestors: Seq[FormulaOccurrence] = {
      val tmp = parents flatMap { _.ancestors }
      parents ++ tmp
    }

    /**
     * Tests equality of formulas.
     *
     * @param that Another FormulaOccurrence.
     * @return true iff this and that are occurrences of the same formula.
     */
    def =^=( that: FormulaOccurrence ) = this.formula == that.formula
  }

  //FO = FormulaOccurrence
  /**
   * Formula occurrence factory.  This factory is stored in [[FormulaOccurrence]] itself, sometimes passed via an
   * implicit {{{factory}}} parameter, or directly linked to [[defaultFormulaOccurrenceFactory]].
   *
   * Specialized factories can return instances of subclasses of [[FormulaOccurrence]],
   * e.g. [[at.logic.gapt.proofs.lksk.LKskFOFactory]].
   *
   * FIXME: The only supported factory is [[defaultFormulaOccurrenceFactory]] at the moment.
   */
  trait FOFactory {
    def createFormulaOccurrence( formula: HOLFormula, ancestors: Seq[FormulaOccurrence] ): FormulaOccurrence
  }

  /**
   * Creates instances of [[FormulaOccurrence]].
   */
  object defaultFormulaOccurrenceFactory extends FOFactory {
    def createFormulaOccurrence( formula: HOLFormula, ancestors: Seq[FormulaOccurrence] ): FormulaOccurrence =
      new FormulaOccurrence( formula, ancestors, this )

    private var id_counter = 10000
    private[occurrences] def freshId() = { id_counter = id_counter + 1; id_counter }
  }

}

package object occurrences {
  implicit val factory = defaultFormulaOccurrenceFactory

  /**
   * Implicitly converts a [[FormulaOccurrence]] to the formula its occurrence it records.
   */
  implicit def formulaOccurrenceToFormula( fo: FormulaOccurrence ): HOLFormula = fo.formula
}

