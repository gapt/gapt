package at.logic.provers.maxsat

import at.logic.calculi.resolution.FClause

/**
 * Created by frain on 3/31/15.
 */
class ToySAT extends MaxSATSolverBinary {
  def format() = Format.ToySAT
  def noBinaryWarn() = "Please put the toysat binary (available at https://github.com/msakai/toysolver) into PATH"
  def command( in: String, out: String ) = List( "toysat", "--maxsat", in )
  def solve( hard: List[FClause], soft: List[Tuple2[FClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
