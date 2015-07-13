package at.logic.gapt.proofs.lk

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLOrdering
import at.logic.gapt.proofs.lk.base.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object base {
  type HOLSequent = Sequent[HOLFormula]

  implicit class RichFormulaSequent( val sequent: Sequent[HOLFormula] ) {

    def formulas = sequent.elements

    def polarizedFormulas = sequent.polarizedElements

    /**
     * Interpretation of the sequent as a formula.
     * Why is this not the definition of a sequent (/\ F -> \/ G)? The current implementation (\/-F \/ G) is
     * only classically equivalent (In IL a -> b :/- -a \/ b).
     */
    def toFormula: HOLFormula = Or( sequent.antecedent.toList.map( f => Neg( f ) ) ++ sequent.succedent )

    def toNegFormula: HOLFormula = And( sequent.antecedent ++ sequent.succedent.map( Neg( _ ) ) )

    def toImplication: HOLFormula = Imp( And( sequent.antecedent.toList ), Or( sequent.succedent ) )

    def renameSymbols( map: SymbolMap ) = sequent map ( NameReplacement( _, map ) )

  }

  object HOLSequent {
    def apply( ant: Seq[HOLFormula], succ: Seq[HOLFormula] ): HOLSequent = Sequent( ant, succ )

    def apply( polarizedElements: Seq[( HOLFormula, Boolean )] ): HOLSequent = Sequent( polarizedElements )

    def unapply( f: HOLSequent ): Option[( Seq[HOLFormula], Seq[HOLFormula] )] = Some( ( f.antecedent, f.succedent ) )

  }

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
     * Converts to a [[HOLSequent]], ignoring where the formulas occur.
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
