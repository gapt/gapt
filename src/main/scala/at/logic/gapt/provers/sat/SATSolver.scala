package at.logic.gapt.provers.sat

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.expr.{ FOLFormula, HOLFormula }
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.formats.dimacs.{ DIMACSEncoding, DIMACS }
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.lkNew.LKProof
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }
import at.logic.gapt.provers.Prover

abstract class SATSolver extends Prover {

  def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model]

  def solve( cnf: TraversableOnce[HOLClause] ): Option[Interpretation] = {
    val encoding = new DIMACSEncoding
    solve( encoding.encodeCNF( cnf ) ) map { dimacsModel =>
      encoding.decodeModel( dimacsModel )
    }
  }

  // FIXME: rewrite CNF transformation and support non-FOL clauses...
  def solve( formula: HOLFormula ): Option[Interpretation] =
    formula match {
      case formula: FOLFormula => solve( TseitinCNF( formula.asInstanceOf[FOLFormula] ) )
      case _                   => solve( CNFp.toClauseList( formula ) )
    }

  def getLKProof( seq: HOLSequent ): Option[LKProof] = throw new UnsupportedOperationException
  override def isValid( f: HOLFormula ): Boolean = solve( -f ).isEmpty
  override def isValid( seq: HOLSequent ): Boolean = isValid( seq.toFormula )
}
