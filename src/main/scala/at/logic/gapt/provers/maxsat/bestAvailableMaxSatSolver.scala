package at.logic.gapt.provers.maxsat

import at.logic.gapt.formats.dimacs.DIMACS.{ Model, Clause, CNF }

object bestAvailableMaxSatSolver extends MaxSATSolver {
  val bestAvailableSolver =
    Seq( new OpenWBO, new QMaxSAT ).
      find( _.isInstalled ).
      getOrElse( new MaxSat4j )

  override def solve( hard: CNF, soft: Seq[( Clause, Int )] ): Option[Model] =
    bestAvailableSolver.solve( hard, soft )
}
