package at.logic.gapt.proofs

import at.logic.gapt.expr.{ FOLFormula, HOLFormula }
import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object resolution {
  type Clause[+A] = Sequent[A]

  type OccClause = Clause[FormulaOccurrence]

  //FIXME: This should be Clause[HOLAtom], but HOLAtom is currently not a type.
  type HOLClause = Clause[HOLFormula]

  //FIXME: This should be Clause[FOLAtom], but FOLAtom is currently not a type.
  type FOLClause = Clause[FOLFormula]

  implicit class RichClause[+A]( clause: Clause[A] ) {
    def negative = clause.antecedent

    def positive = clause.succedent

    def literals = ( negative map { f => ( f, false ) } ) ++ ( positive map { f => ( f, true ) } )
  }
}
