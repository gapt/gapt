package at.logic.gapt.provers.maxsat

class ToySolver extends ExternalMaxSATSolver {
  def command = List( "toysolver", "--maxsat" )
}
