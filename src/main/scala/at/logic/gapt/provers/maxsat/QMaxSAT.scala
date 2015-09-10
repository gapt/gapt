package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

/**
 * Created by frain on 3/31/15.
 */
class QMaxSAT extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "Please put the qmaxsat binary (available at https://sites.google.com/site/qmaxsat/) into PATH"
  def command( in: String, out: String ) = List( "qmaxsat", in, out )
  def solve( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
