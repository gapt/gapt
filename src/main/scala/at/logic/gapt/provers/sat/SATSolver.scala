package at.logic.gapt.provers.sat

import at.logic.gapt.expr.hol.structuralCNF
import at.logic.gapt.expr.{ HOLAtomConst, HOLFormula }
import at.logic.gapt.formats.dimacs.{ DIMACSEncoding, DIMACS }
import at.logic.gapt.models.{ MapBasedInterpretation, Interpretation }
import at.logic.gapt.proofs.lkNew.LKProof
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }
import at.logic.gapt.provers.{ OneShotProver, Prover }

abstract class SATSolver extends OneShotProver {

  def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model]

  def solve( cnf: TraversableOnce[HOLClause] ): Option[Interpretation] = {
    val encoding = new DIMACSEncoding
    solve( encoding.encodeCNF( cnf ) ) map { dimacsModel =>
      encoding.decodeModel( dimacsModel )
    }
  }

  def solve( formula: HOLFormula ): Option[Interpretation] = {
    val ( cnf, _, definitions ) = structuralCNF( formula, generateJustifications = false, propositional = true )
    solve( cnf ) map {
      case i: MapBasedInterpretation =>
        // remove abbreviations for subformulas
        new MapBasedInterpretation( i.model.filterKeys {
          case c: HOLAtomConst => !definitions.isDefinedAt( c )
          case _               => true
        } )
      case i => i
    }
  }

  def getLKProof( seq: HOLSequent ): Option[LKProof] = throw new UnsupportedOperationException
  override def isValid( f: HOLFormula ): Boolean = solve( -f ).isEmpty
  override def isValid( seq: HOLSequent ): Boolean = isValid( seq.toFormula )
}
