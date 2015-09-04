package at.logic.gapt.provers.maxsat

import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.resolution.HOLClause

object bestAvailableMaxSatSolver extends MaxSATSolver {
  val bestAvailableSolver =
    Seq( new OpenWBO, new QMaxSAT ).
      find( _.isInstalled ).
      getOrElse( new MaxSat4j )

  override def solve( hard: List[HOLClause], soft: List[( HOLClause, Int )] ): Option[Interpretation] =
    bestAvailableSolver.solve( hard, soft )
}
