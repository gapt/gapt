package at.logic.gapt.provers.maxsat

class MiniMaxSAT extends ExternalMaxSATSolver {
  def command = List( "minimaxsat", "-F=2" )
}
