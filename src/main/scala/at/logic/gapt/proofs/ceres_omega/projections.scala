/*
 * projections.scala
 *
 */

package at.logic.gapt.proofs.ceres_omega.projections

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.ceres.ProjectionException
import at.logic.gapt.proofs.lkskNew.LKskProof.LabelledFormula
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.proofs.ceres.Pickrule._

object Projections extends at.logic.gapt.utils.logging.Logger {

  def reflexivity_projection( proof: LKskProof, t: TA = Ti ): LKskProof = {
    val es = proof.endSequent
    val x = Var( "x", t )

    var count = 0
    val x_ = rename( x, es.formulas.flatMap( freeVariables( _ ) ).toList ).asInstanceOf[Var]
    val ax: LKskProof = Axiom( Nil, List( Eq( x_, x_ ) ) )
    val left = es.antecedent.foldLeft( ax )( ( p, f ) => WeakeningLeft( p, f ) )
    val right = es.succedent.foldLeft( left )( ( p, f ) => WeakeningRight( p, f ) )
    right
  }

  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKskProof ): Set[LKskProof] =
    apply( proof, proof.endSequent.map( _ => false ), x => true )

  def apply( proof: LKskProof, pred: HOLFormula => Boolean ): Set[LKskProof] =
    apply( proof, proof.endSequent.map( _ => false ), pred )

  def apply( proof: LKskProof, cut_ancs: Sequent[Boolean], pred: HOLFormula => Boolean ): Set[LKskProof] = {
    implicit val c_ancs = cut_ancs
    proof.occConnectors
    try {
      val r: Set[LKskProof] = proof match {
        /* Structural rules except cut */
        case Axiom( s )                    => Set( proof )

        case ContractionLeft( p, a1, a2 )       => handleContractionRule( proof, p, a1, a2, ContractionLeft.apply, pred )
        case ContractionRight( p, a1, a2 )      => handleContractionRule( proof, p, a1, a2, ContractionRight.apply, pred )
        case WeakeningLeft( p, m )              => handleWeakeningRule( proof, p, m, WeakeningLeft.apply, pred )
        case WeakeningRight( p, m )             => handleWeakeningRule( proof, p, m, WeakeningRight.apply, pred )

        /* Logical rules */
        case AndRight( p1, a1, p2, a2 )         => handleBinaryRule( proof, p1, p2, a1, a2, AndRight.apply, pred )
        case OrLeft( p1, a1, p2, a2 )           => handleBinaryRule( proof, p1, p2, a1, a2, OrLeft.apply, pred )
        case ImpLeft( p1, a1, p2, a2 )          => handleBinaryRule( proof, p1, p2, a1, a2, ImpLeft.apply, pred )
        case NegLeft( p, a )                    => handleNegRule( proof, p, a, NegLeft.apply, pred )
        case NegRight( p, a )                   => handleNegRule( proof, p, a, NegRight.apply, pred )
        case OrRight( p, a1, a2 )               => handleUnaryRule( proof, p, a1, a2, OrRight.apply, pred )
        case AndLeft( p, a1, a2 )               => handleUnaryRule( proof, p, a1, a2, AndLeft.apply, pred )
        case ImpRight( p, a1, a2 )              => handleUnaryRule( proof, p, a1, a2, ImpRight.apply, pred )

        /* quantifier rules  */
        case AllRight( p, a, eigenv, qvar )     => handleStrongQuantRule( proof, p, AllRight.apply, pred )
        case ExLeft( p, a, eigenvar, qvar )     => handleStrongQuantRule( proof, p, ExLeft.apply, pred )
        case AllLeft( p, a, f, t, v )        => handleWeakQuantRule( proof, p, a, f, t, v, AllLeft.apply, pred )
        case ExRight( p, a, f, t, v )       => handleWeakQuantRule( proof, p, a, f, t, v, ExRight.apply, pred )

        case EqualityLeft( p1, e, a, pos )      => handleEqRule( proof, p1, e, a, pos, EqualityLeft.apply, pred )
        case EqualityRight( p1, e, a, pos )     => handleEqRule( proof, p1, e, a, pos, EqualityRight.apply, pred )
        case rule @ Cut( p1, a1, p2, a2 ) =>
          if ( pred( rule.cutFormula ) ) {
            /* this cut is taken into account */
            val new_cut_ancs_left = mapToUpperProof( proof.occConnectors( 0 ), cut_ancs, true )
            val new_cut_ancs_right = mapToUpperProof( proof.occConnectors( 1 ), cut_ancs, true )
            require( new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
            require( new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
            val s1 = apply( p1, new_cut_ancs_left, pred )
            val s2 = apply( p2, new_cut_ancs_right, pred )
            handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs_left, new_cut_ancs_right )
          } else {
            /* this cut is skipped */
            val new_cut_ancs_left = mapToUpperProof( proof.occConnectors( 0 ), cut_ancs, false )
            val new_cut_ancs_right = mapToUpperProof( proof.occConnectors( 1 ), cut_ancs, false )
            require( new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
            require( new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
            val s1 = apply( p1, new_cut_ancs_left, pred )
            val s2 = apply( p2, new_cut_ancs_right, pred )
            s1.foldLeft( Set.empty[LKskProof] )( ( s, pm1 ) =>
              s ++ s2.map( pm2 => {
                val List( aux1, aux2 ) = pickrule( proof, List( p1, p2 ), List( pm1, pm2 ), List( a1, a2 ) )
                Cut( p1, aux1, p2, aux2 )
              } ) )
          }
        case _ => throw new Exception( "No such a rule in Projections.apply" )
      }
      r
    } catch {
      case e: ProjectionException =>
        //println("passing exception up...")
        //throw ProjectionException(e.getMessage, proof, Nil, null)
        throw e
      case e: Exception =>
        throw ProjectionException( "Error computing projection: " + e.getMessage + sys.props( "line.separator" ) + e.getStackTrace, proof, Nil, e )
    }
  }

  /* finds the cut ancestor sequent in the parent connected with the occurrence connector */
  def copySetToAncestor( connector: OccConnector[HOLFormula], s: Sequent[Boolean] ) = {
    connector.parents( s ).map( _.head )
  }

  /* traces the ancestor relationship to infer cut-formulas in the parent proof. if a formula does not have parents,
     use default */
  private def mapToUpperProof[Formula]( conn: OccConnector[Formula], cut_occs: Sequent[Boolean], default: Boolean ) =
    conn.parents( cut_occs ).map( _.headOption getOrElse default )

  def handleBinaryESAnc( proof: LKskProof, parent1: LKskProof, parent2: LKskProof, s1: Set[LKskProof], s2: Set[LKskProof],
                         constructor: ( LKskProof, SequentIndex, LKskProof, SequentIndex ) => LKskProof ) =
    s1.foldLeft( Set.empty[LKskProof] )( ( s, p1 ) =>
      s ++ s2.map( p2 => {
        val List( a1, a2 ) = pickrule( proof, List( parent1, parent2 ), List( p1, p2 ), List( proof.auxIndices( 0 )( 0 ), proof.auxIndices( 1 )( 0 ) ) )
        constructor( p1, a1, p2, a2 )
      } ) )

  def getESAncs( proof: LKskProof, cut_ancs: Sequent[Boolean] ): HOLSequent =
  //use cut_ancs as characteristic function to filter the the cut-ancestors from the current sequent
    ( proof.endSequent zip cut_ancs ).filterNot( _._2 ).map( _._1 )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKskProof, p1: LKskProof, p2: LKskProof,
                          s1: Set[LKskProof], s2: Set[LKskProof],
                          cut_ancs1: Sequent[Boolean], cut_ancs2: Sequent[Boolean] ): Set[LKskProof] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs2 ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs1 ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  //TODO: this a duplication of some function lk
  def weakenESAncs( esancs: HOLSequent, s: Set[LKskProof] ) = {
    val wl = s.map( p => esancs.antecedent.foldLeft( p )( ( p, fo ) => WeakeningLeft( p, fo ) ) )
    wl.map( p => esancs.succedent.foldLeft( p )( ( p, fo ) => WeakeningRight( p, fo ) ) )
  }

  def handleContractionRule[Side <: SequentIndex]( proof: LKskProof, p: LKskProof,
                             a1: SequentIndex, a2: SequentIndex,
                             constructor: ( LKskProof, Side, Side ) => LKskProof,
                             pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      constructor( pm, a1_, a2_ )
    } )
  }

  //implication does not weaken the second argument, we need two occs
  def handleUnaryRule[T]( proof: LKskProof, p: LKskProof, a1: SequentIndex, a2: SequentIndex,
                          constructor: ( LKskProof, SequentIndex, SequentIndex ) => LKskProof,
                          pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      constructor( pm, a1_, a2_ )
    } )
  }

  def handleWeakeningRule( proof: LKskProof, p: LKskProof, m: LabelledFormula,
                           constructor: ( LKskProof, LabelledFormula ) => LKskProof,
                           pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val maincutanc = cut_ancs( proof.mainIndices( 0 ) )
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => constructor( pm, m ) )
  }

  def handleDefRule( proof: LKskProof, p: LKskProof, a: SequentIndex, f: HOLFormula,
                     constructor: ( LKskProof, SequentIndex, HOLFormula ) => LKskProof,
                     pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_, f )
    } )
  }

  def handleNegRule( proof: LKskProof, p: LKskProof, a: SequentIndex,
                     constructor: ( LKskProof, SequentIndex ) => LKskProof,
                     pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_ )
    } )
  }

  def handleWeakQuantRule( proof: LKskProof, p: LKskProof, a: SequentIndex, f: HOLFormula, t: LambdaExpression, qvar: Var,
                           constructor: ( LKskProof, SequentIndex, HOLFormula, LambdaExpression, Var ) => LKskProof,
                           pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_, f, t, qvar )
    } )
  }

  def handleBinaryRule( proof: LKskProof, p1: LKskProof, p2: LKskProof, a1: SequentIndex, a2: SequentIndex,
                        constructor: ( LKskProof, SequentIndex, LKskProof, SequentIndex ) => LKskProof,
                        pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ) = {
    val new_cut_ancs1 = copySetToAncestor( proof.occConnectors( 0 ), cut_ancs )
    val new_cut_ancs2 = copySetToAncestor( proof.occConnectors( 1 ), cut_ancs )
    val s1 = apply( p1, new_cut_ancs1, pred )
    val s2 = apply( p2, new_cut_ancs2, pred )
    // val nLine = sys.props("line.separator")
    //println("Binary rule on:"+nLine+s1.map(_.root)+nLine+s2.map(_.root))
    if ( cut_ancs( proof.mainIndices( 0 ) ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs1, new_cut_ancs2 )
    else
      handleBinaryESAnc( proof, p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKskProof, p: LKskProof, e: SequentIndex, a: SequentIndex,
                    pos: HOLPosition, constructor: ( LKskProof, SequentIndex, SequentIndex, HOLPosition ) => LKskProof,
                    pred: HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ) = {
    val new_cut_ancs = copySetToAncestor( proof.occConnectors( 0 ), cut_ancs )
    val s1 = apply( p, new_cut_ancs, pred )
    ( cut_ancs( proof.mainIndices( 0 ) ), cut_ancs( proof.mainIndices( 1 ) ) ) match {
      case ( true, true ) =>
        s1
      case ( false, false ) =>
        s1 map ( pm => {
          val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( e, a ) )
          constructor( p, a1_, a2_, pos )
        } )

      case ( false, true ) =>
        val ef = p.endSequent( e )
        val ax = Axiom( List( ef ), List( ef ) )
        val main_e = proof.mainIndices( 0 )
        val es = proof.endSequent.zipWithIndex.filter( x => x._2 != main_e && !cut_ancs( x._2 ) ).map( _._1 )
        val wax = weakenESAncs( es, Set( ax ) )
        s1 ++ wax
      case ( true, false ) =>
        s1
    }
  }

  def handleStrongQuantRule( proof: LKskProof, p: LKskProof,
                             constructor: ( LKskProof, SequentIndex, Var, Var ) => LKskProof,
                             pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKskProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else throw new Exception( "The proof is not skolemized!" )
  }
}

