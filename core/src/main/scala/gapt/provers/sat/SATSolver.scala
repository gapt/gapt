package gapt.provers.sat

import gapt.expr.hol.fastStructuralCNF
import gapt.expr.{ Formula, HOLAtomConst }
import gapt.formats.dimacs.{ DIMACS, DIMACSEncoding }
import gapt.models.PropositionalModel
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.{ Factor, Input, ResolutionProof }
import gapt.proofs.rup.RupProof
import gapt.proofs.{ Context, HOLClause, HOLSequent, MutableContext, Sequent }
import gapt.provers.{ OneShotProver, ResolutionProver }
import gapt.utils.Maybe

trait SATSolver extends OneShotProver {

  def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model]

  def solve( cnf: TraversableOnce[HOLClause] ): Option[PropositionalModel] = {
    val encoding = new DIMACSEncoding
    solve( encoding.encodeCNF( cnf ) ) map { dimacsModel =>
      encoding.decodeModel( dimacsModel )
    }
  }

  def solve( formula: Formula ): Option[PropositionalModel] = {
    val ( cnf, definitions ) = fastStructuralCNF()( formula )
    solve( cnf ) map { i =>
      // remove abbreviations for subformulas
      PropositionalModel( Map() ++ i.assignment.filterKeys {
        case c: HOLAtomConst => !definitions.isDefinedAt( c )
        case _               => true
      } )
    }
  }

  def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = throw new UnsupportedOperationException
  override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = solve( seq.toNegConjunction ).isEmpty

  /**
   * Checks whether a set of clauses is propositionally unsatisfiable.
   */
  override def isUnsat( cnf: Iterable[HOLClause] )( implicit ctx: Maybe[Context] ): Boolean = isValid( cnf ++: Sequent() map { _.toDisjunction } )
}

trait DrupSolver extends SATSolver with ResolutionProver {

  def getDrupProof( cnf: DIMACS.CNF ): Option[RupProof]

  def getDrupProof( formula: Formula ): Option[RupProof] = getDrupProof( Sequent() :+ formula )
  def getDrupProof( sequent: HOLSequent ): Option[RupProof] =
    getDrupProof( fastStructuralCNF()( sequent )._1 )
  def getDrupProof( cnf: Traversable[HOLClause] ): Option[RupProof] = {
    val encoding = new DIMACSEncoding
    val dimacsCNF = encoding.encodeCNF( cnf )
    getDrupProof( dimacsCNF )
  }

  override def getResolutionProof( cnf: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] = {
    val cnf_ = cnf.map( c => Factor( Input( c ) ) )
    val encoding = new DIMACSEncoding
    val dimacsCNF = encoding.encodeCNF( cnf_.view.map( _.conclusion.asInstanceOf[HOLClause] ) )
    getDrupProof( dimacsCNF ).map( _.toRes.toResolution(
      encoding.decodeAtom,
      cls => {
        val clause = encoding.decodeClause( cls.toSeq )
        cnf_.find( _.conclusion multiSetEquals clause ).get
      } ) )
  }

  override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = super[SATSolver].isValid( seq )
  override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = super[ResolutionProver].getLKProof( sequent )
}