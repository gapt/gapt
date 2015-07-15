package at.logic.gapt.proofs

import at.logic.gapt.expr.{ FOLAtom, HOLAtom }
import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object resolution {
  type Clause[+A] = Sequent[A]

  type OccClause = Clause[FormulaOccurrence]

  type HOLClause = Clause[HOLAtom]

  type FOLClause = Clause[FOLAtom]

  implicit class RichClause[+A]( val clause: Clause[A] ) {
    def negative = clause.antecedent

    def positive = clause.succedent

    def literals = ( negative map { f => ( f, false ) } ) ++ ( positive map { f => ( f, true ) } )
  }

  implicit class RichOccClause( clause: OccClause ) extends RichClause[FormulaOccurrence]( clause ) {
    def toHOLClause: HOLClause = clause map { l =>
      if ( l.formula.isInstanceOf[HOLAtom] )
        l.formula.asInstanceOf[HOLAtom]
      else
        ???
    }
  }
}
