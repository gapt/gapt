package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

/**
 * Created by frain on 3/31/15.
 */
class ToySolver extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "Please put the toysolver binary (available at https://github.com/msakai/toysolver) into PATH"
  def command = List( "toysolver", "--maxsat" )
  def solve( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
