package at.logic.gapt.provers.maxsat

import at.logic.gapt.proofs.HOLClause

class MiFuMaX extends MaxSATSolverBinary {
  def format() = Format.MultiVLine
  def noBinaryWarn() = "mifumax is not installed"
  def command = List( "mifumax" )
  def solve( hard: List[HOLClause], soft: List[( HOLClause, Int )] ) =
    getFromMaxSATBinary( hard, soft )
}
