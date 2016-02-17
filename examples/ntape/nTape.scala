package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr.fol.{ reduceHolToFol, undoHol2Fol, replaceAbstractions }
import at.logic.gapt.formats.llkNew.ExtendedProofDatabase
import at.logic.gapt.proofs.lkskNew.LKskToExpansionProof
import at.logic.gapt.proofs.{ Sequent, HOLClause }
import at.logic.gapt.proofs.ceres_omega._
import at.logic.gapt.proofs.resolution.Robinson2RalWithAbstractions
import at.logic.gapt.provers.prover9.Prover9

import scala.collection.immutable.SortedMap

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
  lazy val postprocessed_lkproof = AtomicExpansion( DefinitionElimination( proofdb.Definitions )( regularize( proofdb proof root_proof ) ) )

  /**
   * The processed input proof converted to LKsk.
   */
  lazy val lksk_proof = LKToLKsk( postprocessed_lkproof )

  /**
   * The struct of the proof. It is an intermediate representation of the characteristic sequent set.
   */
  lazy val struct = extractStructFromLKsk( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The set of projections of the input proof.
   */
  lazy val projections = Projections( lksk_proof, ceres_omega.skip_propositional )

  /**
   * The characteristic sequent set of the input proof.
   */
  lazy val css = StandardClauseSet( struct )

  /**
   * The first order export of the characteristic sequent set, together with the map of replacing constants.
   */
  lazy val ( abstracted_constants_map, fol_css ) = {
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
  lazy val fol_refutation = Prover9.getRobinsonProof( fol_css ) match {
    case None =>
      throw new Exception( "Could not refute clause set!" )
    case Some( rp ) =>
      rp
  }

  /**
   * The ral version of the first-order refutation, with all necessary simplifications undone
   */
  lazy val ral_refutation = {
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
  lazy val acnf = ceres_omega( projections, ral_refutation, lksk_proof.conclusion, struct )._1

  /**
   * The expansion proof of the cut-free proof
   */
  lazy val expansion_proof = LKskToExpansionProof( acnf )

  //prints the interesting terms from the expansion sequent
  def printStatistics() = {

    val conjuncts = decompose( expansion_proof.expansionSequent.antecedent( 1 ) )
    // FIXME: use a less fragile method to find the induction formula...
    val indet = conjuncts( 19 )

    val List( ind1, ind2 ): List[ExpansionTree] = indet match {
      case ETWeakQuantifier( _, instances ) =>
        instances.map( _._2 ).toList
    }

    val ( ind1base, ind1step ) = ind1 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    val ( ind2base, ind2step ) = ind2 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, base_instances ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, step_instances ) )
          )
        ), _ ) =>
        val List( ( base, _ ) ) = base_instances.toList
        val List( ( step, _ ) ) = step_instances.toList
        ( base, step )
    }

    ( ind1base, ind1step, ind2base, ind2step ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        val map = Map[LambdaExpression, StringSymbol]()
        val counter = new { private var state = 0; def nextId = { state = state + 1; state } }

        val ( map1, sb1 ) = replaceAbstractions( sb, map, counter )
        val ( map2, ss1 ) = replaceAbstractions( ss, map1, counter )
        val ( map3, tb1 ) = replaceAbstractions( tb, map2, counter )
        val ( map4, ts1 ) = replaceAbstractions( ts, map3, counter )

        println( "base 1 simplified: " + Abs( xb, sb1 ) )
        println( "base 2 simplified: " + Abs( yb, tb1 ) )
        println( "step 1 simplified: " + Abs( xs, ss1 ) )
        println( "step 2 simplified: " + Abs( ys, ts1 ) )

        println( "With shortcuts:" )
        for ( ( term, sym ) <- map4 ) {
          println( "Symbol: " + sym )
          println( "Term:   " + term )
        }
    }

  }

  private def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }

}
