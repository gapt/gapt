package at.logic.gapt.provers.maxsat

class ToySAT extends ExternalMaxSATSolver {
  def command = List( "toysat", "--maxsat" )
}
