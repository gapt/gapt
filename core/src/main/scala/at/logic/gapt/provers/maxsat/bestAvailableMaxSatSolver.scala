package at.logic.gapt.provers.maxsat

import at.logic.gapt.formats.dimacs.DIMACS.{ Model, Clause, CNF }

object bestAvailableMaxSatSolver extends MaxSATSolver {
  private val bestAvailableSolver =
    Seq( OpenWBO, QMaxSAT ).
      find( _.isInstalled ).
      getOrElse( MaxSat4j )

  override def solve( hard: CNF, soft: Seq[( Clause, Int )] ): Option[Model] =
    bestAvailableSolver.solve( hard, soft )
}
