package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.fol.{ reduceHolToFol, undoHol2Fol, replaceAbstractions }
import at.logic.gapt.formats.llkNew.ExtendedProofDatabase
import at.logic.gapt.proofs.{ Sequent, HOLClause }
import at.logic.gapt.proofs.ceres_omega._
import at.logic.gapt.proofs.resolution.Robinson2RalWithAbstractions
import at.logic.gapt.provers.prover9.Prover9

/**
 * The generic template for the nTape proofs.
 */
abstract class nTape {
  /** The proof database to start from. */
  def proofdb(): ExtendedProofDatabase

  /** The name of the root proof to start with */
  def root_proof(): String

  /**
   * The input proof (TAPEPROOF) after definition elimination, expansion of logical axioms to atomic axioms and
   *  definition eliminiation
   */
  val postprocessed_lkproof = AtomicExpansion( DefinitionElimination( proofdb.Definitions )( regularize( proofdb proof root_proof ) ) )

  /**
   * The processed input proof converted to LKsk.
   */
  val lksk_proof = LKToLKsk( postprocessed_lkproof )

  /**
   * The struct of the proof. It is an intermediate representation of the characteristic sequent set.
   */
  val struct = extractStructFromLKsk( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The set of projections of the input proof.
   */
  val projections = Projections( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The characteristic sequent set of the input proof.
   */
  val css = StandardClauseSet( struct )

  /**
   * The first order export of the characteristic sequent set, together with the map of replacing constants.
   */
  val ( abstracted_constants_map, fol_css ) = {
    val css_nolabels = css.map( _.map( _._2 ) ).toList // remove labels from css
    val ( abs_consts, abs_css ) = replaceAbstractions( css_nolabels )
    /* map types to first order*/
    val fol_css = reduceHolToFol( abs_css )
    /* converting to clause form, this is cleaner than casting */
    val fol_ccs = fol_css map {
      case Sequent( ant, succ ) =>
        HOLClause(
          ant map { case atom @ FOLAtom( _, _ ) => atom },
          succ map { case atom @ FOLAtom( _, _ ) => atom }
        )
    }
    ( abs_consts, fol_ccs )
  }

  /**
   * The first order refutation of the first order characteristic sequent set
   */
  val fol_refutation = Prover9.getRobinsonProof( fol_css ) match {
    case None =>
      throw new Exception( "Could not refute clause set!" )
    case Some( rp ) =>
      rp
  }

  /**
   * The ral version of the first-order refutation, with all necessary simplifications undone
   */
  val ral_refutation = {
    val proofformulas = for ( p <- lksk_proof.subProofs; f <- p.formulas.elements ) yield f

    val ( sigc, sigv ) = undoHol2Fol.getSignature( proofformulas.toList )

    val converter = Robinson2RalWithAbstractions(
      sigv.map( x => ( x._1, x._2.toList ) ),
      sigc.map( x => ( x._1, x._2.toList ) ), abstracted_constants_map
    )

    converter( fol_refutation )
  }

  /**
   * The simulation of the ral refutation on the projections i.e. an LKsk proof where cuts only work on atom formulas
   */
  val acnf = ceres_omega( projections, ral_refutation, lksk_proof.conclusion, struct )._1

}
