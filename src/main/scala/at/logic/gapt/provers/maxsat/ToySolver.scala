package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.resolution.FClause

/**
 * Created by frain on 3/31/15.
 */
class ToySolver extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "Please put the toysolver binary (available at https://github.com/msakai/toysolver) into PATH"
  def command( in: String, out: String ) = List( "toysolver", "--maxsat", in )
  def solve( hard: List[FClause], soft: List[Tuple2[FClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
