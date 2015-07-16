package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.resolution.FClause

class MiFuMaX extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "mifumax is not installed"
  def command( in: String, out: String ) = List( "mifumax", in, out )
  def solve( hard: List[FClause], soft: List[( FClause, Int )] ) =
    getFromMaxSATBinary( hard, soft )
}
