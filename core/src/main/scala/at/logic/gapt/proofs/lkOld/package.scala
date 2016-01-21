package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object base {

  type OccSequent = Sequent[FormulaOccurrence]

  implicit class RichOccSequent( val sequent: Sequent[FormulaOccurrence] ) {
    /**
     * Removes the specified [[at.logic.gapt.proofs.occurrences.FormulaOccurrence]]s from each side.
     */
    def removeFormulasAtOccurrences( occs: Seq[FormulaOccurrence] ): OccSequent = sequent filterNot { x => occs contains x }

    /**
     * Finds the first occurrence in this sequent having the given ancestor.
     */
    def getChildOf( ancestor: FormulaOccurrence ): Option[FormulaOccurrence] = sequent.elements find { _.parents.contains( ancestor ) }

    /**
     * Converts to a [[at.logic.gapt.proofs.HOLSequent]], ignoring where the formulas occur.
     */
    def toHOLSequent: HOLSequent = sequent map { _.formula }

    /**
     * Interpretation of the sequent as formula.
     */
    def toFormula = this.toHOLSequent.toFormula

    /**
     * Is this sequent of the form F :- F?
     */
    def isTaut = sequent.antecedent.size == 1 && sequent.succedent.size == 1 && sequent.antecedent.head.formula == sequent.succedent.head.formula

    /**
     * Occurrences on both sides of the sequent, i.e. the concatenation of antecedent and succedent.
     */
    def occurrences = sequent.elements

    /**
     * Is this sequent of the form :- t = t?
     */
    def isReflexivity = sequent.antecedent.size == 0 && sequent.succedent.size == 1 && (
      sequent.succedent.head.formula match {
        case Eq( s, t ) => ( s == t )
        case _          => false
      }
    )

    def freeVariables: Set[Var] = this.toHOLSequent.formulas.toSet.flatMap( ( f: HOLFormula ) => at.logic.gapt.expr.freeVariables( f ) )

    /**
     * Equality treating each side as a multiset of formulas, ignoring the occurrence.
     */
    def syntacticMultisetEquals( o: OccSequent ) = this.toHOLSequent multiSetEquals o.toHOLSequent

    /**
     * Equality treating each side as a multiset of formulas, ignoring the occurrence.
     */
    def syntacticMultisetEquals( o: HOLSequent )( implicit dummy: DummyImplicit ) = this.toHOLSequent multiSetEquals o

    def =^( o: OccSequent ) = this syntacticMultisetEquals o

  }

  object OccSequent {
    def apply( antecedent: Seq[FormulaOccurrence], succedent: Seq[FormulaOccurrence] ) = new OccSequent( antecedent, succedent )
    def unapply( so: OccSequent ) = Some( so.antecedent, so.succedent )
  }

}
