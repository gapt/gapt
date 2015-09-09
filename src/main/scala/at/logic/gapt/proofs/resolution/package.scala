package at.logic.gapt.proofs

import at.logic.gapt.expr.{ FOLAtom, HOLAtom }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object resolution {
  type OccClause = Clause[FormulaOccurrence]

  implicit class RichOccClause( clause: OccClause ) extends RichClause[FormulaOccurrence]( clause ) {
    def toHOLClause: HOLClause = clause map { l =>
      if ( l.formula.isInstanceOf[HOLAtom] )
        l.formula.asInstanceOf[HOLAtom]
      else
        ???
    }
  }
}
