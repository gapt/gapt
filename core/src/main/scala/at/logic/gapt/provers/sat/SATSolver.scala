package at.logic.gapt.provers.sat

import at.logic.gapt.expr.hol.fastStructuralCNF
import at.logic.gapt.expr.{ HOLAtomConst, Formula }
import at.logic.gapt.formats.dimacs.{ DIMACS, DIMACSEncoding }
import at.logic.gapt.models.{ Interpretation, MapBasedInterpretation }
import at.logic.gapt.proofs.drup.{ DrupProof, DrupToResolutionProof }
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

  def solve( formula: Formula ): Option[Interpretation] = {
    val ( cnf, definitions ) = fastStructuralCNF()( formula )
    solve( cnf ) map {
      case i: MapBasedInterpretation =>
        // remove abbreviations for subformulas
        MapBasedInterpretation( Map() ++ i.model.filterKeys {
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

  def getDrupProof( formula: Formula ): Option[DrupProof] = getDrupProof( Sequent() :+ formula )
  def getDrupProof( sequent: HOLSequent ): Option[DrupProof] =
    getDrupProof( fastStructuralCNF()( sequent )._1 )
  def getDrupProof( cnf: Traversable[HOLClause] ): Option[DrupProof] = {
    val encoding = new DIMACSEncoding
    val dimacsCNF = encoding.encodeCNF( cnf )
    getDrupProof( dimacsCNF ) map { dimacsDRUP =>
      DrupProof( cnf.toSet, encoding decodeProof dimacsDRUP )
    }
  }

  override def getResolutionProof( cnf: Traversable[HOLClause] ): Option[ResolutionProof] =
    getDrupProof( cnf ) map { DrupToResolutionProof( _ ) }

  override def isValid( seq: HOLSequent ): Boolean = super[SATSolver].isValid( seq )
  override def getLKProof( sequent: HOLSequent ): Option[LKProof] = super[ResolutionProver].getLKProof( sequent )
}