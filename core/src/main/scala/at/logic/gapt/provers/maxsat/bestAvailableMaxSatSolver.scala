package at.logic.gapt.provers.maxsat

import at.logic.gapt.formats.dimacs.DIMACS.{ Model, Clause, CNF }

object bestAvailableMaxSatSolver extends MaxSATSolver {
  val actualSolver =
    Seq( OpenWBO, QMaxSAT ).
      find( _.isInstalled ).
      getOrElse( MaxSat4j )

  override def solve( hard: CNF, soft: Seq[( Clause, Int )] ): Option[Model] =
    actualSolver.solve( hard, soft )
}
