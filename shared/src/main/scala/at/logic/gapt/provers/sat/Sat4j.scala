package at.logic.gapt.provers.sat

import at.logic.gapt.formats.dimacs.DIMACS
import org.sat4j.core.{ VecInt, Vec }
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.{ ContradictionException, IVec, IVecInt }

class Sat4j extends SATSolver {
  import Sat4j._

  override def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model] = {
    val solver = SolverFactory.newDefault()
    solver.newVar( DIMACS maxAtom cnf )

    try {
      solver.addAllClauses( cnf )

      if ( solver.isSatisfiable ) {
        Some( solver.model() )
      } else {
        None
      }
    } catch {
      case _: ContradictionException => None
    }
  }
}

object Sat4j extends Sat4j {
  implicit def clause2sat4j( clause: DIMACS.Clause ): IVecInt =
    new VecInt( clause toArray )

  implicit def cnf2sat4j( cnf: DIMACS.CNF ): IVec[IVecInt] =
    new Vec( cnf.map { implicitly[IVecInt]( _ ) }.toArray )
}
