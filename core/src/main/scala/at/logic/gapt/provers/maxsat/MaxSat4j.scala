package at.logic.gapt.provers.maxsat

import java.math.BigInteger
import at.logic.gapt.formats.dimacs.DIMACS
import at.logic.gapt.provers.sat.Sat4j
import org.sat4j.maxsat.WeightedMaxSatDecorator
import org.sat4j.specs.ContradictionException

object MaxSat4j extends MaxSat4j
class MaxSat4j extends MaxSATSolver {
  import Sat4j._

  override def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model] = {
    val threshold = soft.map( _._2 ).sum + 1

    val solver = org.sat4j.pb.SolverFactory.newDefaultOptimizer()
    val decorator = new WeightedMaxSatDecorator( solver )

    decorator.newVar( DIMACS maxAtom ( hard ++ soft.map( _._1 ) ) )
    decorator.setTopWeight( BigInteger.valueOf( threshold ) )

    try {
      hard foreach { decorator.addHardClause( _ ) }
      soft foreach { case ( clause, weight ) => decorator.addSoftClause( weight, clause ) }

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
