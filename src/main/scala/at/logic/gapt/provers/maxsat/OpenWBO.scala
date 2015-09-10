package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

class OpenWBO extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "Please put the open-wbo binary into PATH"
  def command( in: String, out: String ) = List( "open-wbo", in, out )
  def solve( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ) =
    getFromMaxSATBinary( hard, soft )
}
