package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.tptp.TPTPHOLExporter
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.fol.{ reduceHolToFol, replaceAbstractions, undoHol2Fol }
import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.resolution.{ Resolution2RalWithAbstractions, ResolutionToLKProof }
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.{ TimeOutException, withTimeout }

import scala.concurrent.duration.Duration

/**
 * The generic template for using ceres_omega to analyze a proof. It performs the following steps:
 *
 * 1) eliminate definitions ([[AnalysisWithCeresOmega.input_proof]]
 *
 * 2) eliminate definitions ([[AnalysisWithCeresOmega.preprocessed_input_proof1]]
 *
 * 3) expand non-atomic axioms ([[AnalysisWithCeresOmega.preprocessed_input_proof2]])
 *
 * 4) make the proof regular ([[AnalysisWithCeresOmega.preprocessed_input_proof]])
 *
 * 5) convert it to lk_sk ([[AnalysisWithCeresOmega.lksk_proof]])
 *
 * 6) compute the struct, css and projections ([[AnalysisWithCeresOmega.css]],
 *
 *    [[AnalysisWithCeresOmega.projections]], [[AnalysisWithCeresOmega.struct]])
 *
 * 7) map the css to first-order by lambda lifting and erasure of types
 *    ([[AnalysisWithCeresOmega.fol_css]])
 *
 * 8) try to find a refutation of the css
 *    ([[AnalysisWithCeresOmega.fol_refutation]])
 *
 * 9) reintroduce types (might fail because type erasure is a heuristic which is unsound in general)
 *    (no method available, included in step 11)
 *
 * 10) reintroduce terms abstracted away by lambda lifting
 *    (no method available, included in step 11)
 *
 * 11) construct an r_al proof from the refutation
 *    ([[AnalysisWithCeresOmega.ral_refutation]])
 *
 * 12) construct the acnf
 *    ([[AnalysisWithCeresOmega.acnf]])
 *
 * 13) construct the expansion proof (with atomic cuts)
 *    ([[AnalysisWithCeresOmega.expansion_proof]])
 *
 * 14) print statistics
 *    ([[AnalysisWithCeresOmega.printStatistics]])
 */
abstract class AnalysisWithCeresOmega {
  /** The proof database to start from. */
  def proofdb(): ExtendedProofDatabase

  /** The name of the root proof to start with */
  def root_proof(): String

  /** Determines if and which cuts should be taken into accoutn for cut-elimination. Default: propositional cuts are skipped. */
  def skip_strategy() = CERES.skipPropositional( _ )

  /**
   * Timeout for call to theorem provers.
   *
   * @return the timeout as duration. default: 60 seconds
   */
  def timeout(): Duration = Duration( "10s" )

  /**
   * The input LK proof, extracted by the name [[root_proof]] from the proof database ([[proofdb]])
   */
  lazy val input_proof = proofdb proof root_proof

  /**
   * The input proof (TAPEPROOF) after preprocessing step 1: definition elimination
   */
  lazy val preprocessed_input_proof1 = DefinitionElimination( proofdb.Definitions )( input_proof )

  /**
   * The input proof after preprocessing step 2: expansion of logical axioms to atomic axioms
   */
  lazy val preprocessed_input_proof2 = AtomicExpansion( preprocessed_input_proof1 )

  /**
   * The input proof preprocessing step 3: regularization
   */
  lazy val preprocessed_input_proof3 = regularize( preprocessed_input_proof2 )

  /**
   * The input proof (TAPEPROOF) after definition elimination([[preprocessed_input_proof1]], expansion of logical axioms
   * to atomic axioms ([[preprocessed_input_proof2]]) and regularization ([[preprocessed_input_proof3]])
   */
  lazy val preprocessed_input_proof = preprocessed_input_proof3

  /**
   * The processed input proof converted to LKsk.
   */
  lazy val lksk_proof = skolemizeInferences( preprocessed_input_proof )

  /**
   * The struct of the proof. It is an intermediate representation of the characteristic sequent set.
   */
  lazy val struct = extractStruct( lksk_proof, skip_strategy() )

  /**
   * The set of projections of the [[preprocessed_input_proof]].
   */
  lazy val projections = Projections( lksk_proof, skip_strategy() )

  /**
   * The characteristic sequent set of the [[preprocessed_input_proof]].
   */
  lazy val css = StandardClauseSet( struct )

  /**
   * The characteristic sequent set ([[css]]) after removal of labels and subsumption
   */
  lazy val preprocessed_css: List[HOLSequent] = {
    val stripped_css = css
    subsumedClausesRemoval( stripped_css.toList )
  }

  /**
   * The first order export of the preprocessed characteristic sequent set ([[preprocessed_css]]), together with the map of
   * replacing constants.
   */
  lazy val ( abstracted_constants_map, fol_css ) = {
    val css_nolabels = preprocessed_css // remove labels from css
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
   * The first order refutation of the first order characteristic sequent set ([[fol_css]])
   */
  lazy val fol_refutation = {
    val some_rp = try {
      val css = fol_css //evaluate lazy val, otherwise the thread stays blocked
      withTimeout( timeout() ) { Prover9.getResolutionProof( css ) }
    } catch {
      case e: TimeOutException =>
        println( s"Could not refute the clause set within ${timeout()}." )
        throw e
    }

    some_rp match {
      case None =>
        throw new Exception( "Could not refute clause set!" )
      case Some( rp ) =>
        rp
    }
  }

  /**
   * The expansion proof of the first-order refutation ([[fol_refutation]]).
   */
  lazy val fol_refutation_expansion_proof = {
    val lk_rp = ResolutionToLKProof( fol_refutation )
    LKToExpansionProof( lk_rp )
  }

  /**
   * Exports the preprocessed characteristic sequent ([[preprocessed_css]]) set to the TPTP THF format
   *
   * @param filename The name of the file to export to
   */
  def export_thf( filename: String ): Unit = {
    TPTPHOLExporter( preprocessed_css, filename )
  }

  /**
   * The ral version of the first-order refutation ([[fol_refutation]]), with all necessary simplifications undone
   */
  lazy val ral_refutation = {
    val signature = undoHol2Fol.getSignature( lksk_proof, identity[HOLFormula] )

    val converter = Resolution2RalWithAbstractions( signature, abstracted_constants_map )

    converter( fol_refutation )
  }

  /**
   * The simulation of the [[ral_refutation]] on the [[projections]] i.e. an LKsk proof where cuts only work on atom formulas
   */
  lazy val acnf = CERES( lksk_proof.conclusion, projections, ral_refutation )

  /**
   * The expansion proof of the cut-free proof [[acnf]].
   */
  lazy val expansion_proof = LKToExpansionProof( acnf )

  /**
   * A first-order conversion of the deep formula of the [[expansion_proof]].
   */
  lazy val expansion_proof_fol_deep = reduceHolToFol( replaceAbstractions( expansion_proof.expansionSequent.deep.toImplication ) )

  /**
   * The proof of the deep formula of the [[expansion_proof]].
   */
  lazy val reproved_deep = {
    EProver getResolutionProof expansion_proof_fol_deep match {
      case None      => throw new Exception( "Could not reprove deep formula!" )
      case Some( p ) => p
    }
  }

  def thf_reproving_deep( filename: Option[String] ): String = {
    filename match {
      case Some( fn ) =>
        TPTPHOLExporter.apply( expansion_proof.expansionSequent, fn, true, true )
      case None =>
        ()
    }

    TPTPHOLExporter.export( expansion_proof.expansionSequent, true, true )
  }

  def printStatistics() = {
    println( "------------ Proof sizes --------------" )
    println( s"Input proof            : ${input_proof.treeLike.size}" )
    println( s"Preprocessed input     : ${preprocessed_input_proof.treeLike.size}" )
    println( s"LKsk input proof       : ${lksk_proof.treeLike.size}" )
    println( s"ACNF output proof      : ${acnf.treeLike.size}" )
    println( "------------ " )
    println( s"Css size               : ${css.size}" )
    println( s"Preprocessed css size  : ${preprocessed_css.size}" )
    println( "------------ " )
    println( s"Refutation size (dag)  : ${fol_refutation.dagLike.size}" )
    println( s"Refutation size (tree) : ${fol_refutation.treeLike.size}" )
    println( s"Refutation depth       : ${fol_refutation.depth}" )
    println( "------------ " )
    println( s"Reproved deep formula proof size (dag)  : ${reproved_deep.dagLike.size}" )
    println( s"Reproved deep formula proof size (tree) : ${reproved_deep.treeLike.size}" )
  }

  /**
   * Prints the preprocessed characteristic sequent set in TPTP THF format. Use [[export_thf]] to write it to a file.
   */
  def print_css_thf(): Unit = {
    println( TPTPHOLExporter.export_negative( preprocessed_css ) )
  }

}
