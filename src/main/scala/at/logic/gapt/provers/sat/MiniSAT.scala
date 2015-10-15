package at.logic.gapt.provers.sat

class MiniSAT extends ExternalSATSolver {
  override def command: Seq[String] = Seq( "minisat" )
}

object MiniSAT extends MiniSAT