package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

/**
 * Created by frain on 3/31/15.
 */
class ToySAT extends MaxSATSolverBinary {
  def format() = Format.ToySAT
  def noBinaryWarn() = "Please put the toysat binary (available at https://github.com/msakai/toysolver) into PATH"
  def command( in: String, out: String ) = List( "toysat", "--maxsat", in )
  def solve( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
