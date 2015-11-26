package at.logic.gapt.proofs

import at.logic.gapt.expr.{ FOLAtom, HOLAtom }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * Created by sebastian on 7/13/15.
 */
package object resolutionOld {
  type OccClause = Clause[FormulaOccurrence]

  object OccClause {
    def apply( negative: Seq[FormulaOccurrence], positive: Seq[FormulaOccurrence] ): OccClause = {
      require( ( negative ++ positive ).map( _.formula ) forall {
        case HOLAtom( _, _ ) => true
        case _               => false
      } )

      Clause( negative, positive )
    }

    def apply( elements: Seq[( FormulaOccurrence, Boolean )] ): OccClause = {
      require( ( elements map { p => p._1.formula } ) forall {
        case HOLAtom( _, _ ) => true
        case _               => false
      } )

      Clause( elements )
    }
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
