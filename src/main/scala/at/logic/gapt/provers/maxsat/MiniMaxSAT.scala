package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.resolution.HOLClause

/**
 * Created by frain on 3/31/15.
 */
class MiniMaxSAT extends MaxSATSolverBinary {
  def format() = Format.SingleVLine
  def noBinaryWarn() = "Please put the minimaxsat binary (available at https://github.com/izquierdo/tesis_postgrado/tree/master/src/MiniMaxSat) into PATH"
  def command( in: String, out: String ) = List( "minimaxsat", "-F=2", in )
  def solve( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
