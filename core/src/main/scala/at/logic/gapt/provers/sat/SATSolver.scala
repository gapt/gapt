package at.logic.gapt.provers.sat

import at.logic.gapt.expr.hol.structuralCNF
import at.logic.gapt.expr.{ HOLAtomConst, HOLFormula }
import at.logic.gapt.formats.dimacs.{ DIMACS, DIMACSEncoding }
import at.logic.gapt.models.{ Interpretation, MapBasedInterpretation }
import at.logic.gapt.proofs.drup.{ DrupDerive, DrupForget, DrupProof, DrupToResolutionProof }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.provers.{ OneShotProver, ResolutionProver }

trait SATSolver extends OneShotProver {

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
  override def isValid( seq: HOLSequent ): Boolean = solve( seq.toNegConjunction ).isEmpty

  /**
   * Checks whether a set of clauses is propositionally unsatisfiable.
   */
  override def isUnsat( cnf: Iterable[HOLClause] ): Boolean = isValid( cnf ++: Sequent() map { _.toDisjunction } )
}

trait DrupSolver extends SATSolver with ResolutionProver {

  def getDrupProof( cnf: DIMACS.CNF ): Option[DIMACS.DRUP]

  def getDrupProof( formula: HOLFormula ): Option[DrupProof] = getDrupProof( Sequent() :+ formula )
  def getDrupProof( sequent: HOLSequent ): Option[DrupProof] =
    getDrupProof( structuralCNF( sequent, generateJustifications = false, propositional = true )._1 )
  def getDrupProof( cnf: Traversable[HOLClause] ): Option[DrupProof] = {
    val encoding = new DIMACSEncoding
    val dimacsCNF = encoding.encodeCNF( cnf )
    getDrupProof( dimacsCNF ) map { dimacsDRUP =>
      DrupProof( cnf.toSet, encoding decodeProof dimacsDRUP )
    }
  }

  override def getRobinsonProof( cnf: Traversable[HOLClause] ): Option[ResolutionProof] =
    getDrupProof( cnf ) map { DrupToResolutionProof( _ ) }

  override def isValid( seq: HOLSequent ): Boolean = super[SATSolver].isValid( seq )
  override def getLKProof( sequent: HOLSequent ): Option[LKProof] = super[ResolutionProver].getLKProof( sequent )
}