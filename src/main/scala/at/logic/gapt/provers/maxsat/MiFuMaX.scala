package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

class MiFuMaX extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "mifumax is not installed"
  def command( in: String, out: String ) = List( "mifumax", in, out )
  def solve( hard: List[HOLClause], soft: List[( HOLClause, Int )] ) =
    getFromMaxSATBinary( hard, soft )
}
