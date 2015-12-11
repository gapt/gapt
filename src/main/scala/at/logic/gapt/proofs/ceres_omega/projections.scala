/*
 * projections.scala
 *
 */

package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkskNew.LKskProof.{ LabelledSequent, LabelledFormula, Label }
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.proofs.ceres_omega.Pickrule._

case class ProjectionException( message: String, original_proof: LKskProof, new_proofs: List[LKskProof], nested: Exception )
  extends Exception( message, nested ) {}

object Projections extends at.logic.gapt.utils.logging.Logger {
  def reflexivity_projection( es: LabelledSequent, t: Ty = Ti, label: Label ): ( LKskProof, Sequent[Boolean] ) = {
    // create a fresh variable to create x = x
    val ( es_ant, es_succ ) = es.map( _._2 ).toTuple
    val es_formulas = es_ant ++ es_succ
    val es_vars = es_formulas.foldLeft( Set[Var]() )( ( x, y ) => x ++ freeVariables( y ) )
    val x = rename( Var( "x", t ), es_vars.toList )
    val ax: LKskProof = EquationalAxiom( label, Eq( x, x ) )
    val cut_anc = ax.conclusion.map( _ => true )
    weakenESAncs( es, Set( ( ax, cut_anc ) ) ).toList( 0 )
  }

  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKskProof ): Set[( LKskProof, Sequent[Boolean] )] =
    apply( proof, proof.conclusion.map( _ => false ), x => true )

  def apply( proof: LKskProof, pred: HOLFormula => Boolean ): Set[( LKskProof, Sequent[Boolean] )] =
    apply( proof, proof.conclusion.map( _ => false ), pred )

  def apply( proof: LKskProof, cut_ancs: Sequent[Boolean], pred: HOLFormula => Boolean ): Set[( LKskProof, Sequent[Boolean] )] = {
    implicit val c_ancs = cut_ancs
    proof.occConnectors
    try {
      val r: Set[( LKskProof, Sequent[Boolean] )] = proof match {
        /* Structural rules except cut */
        case Axiom( _, _, _ )                  => Set( ( proof, cut_ancs ) )

        case ContractionLeft( p, a1, a2 )      => handleContractionRule( proof, p, a1, a2, ContractionLeft.apply, pred )
        case ContractionRight( p, a1, a2 )     => handleContractionRule( proof, p, a1, a2, ContractionRight.apply, pred )
        case WeakeningLeft( p, m )             => handleWeakeningRule( proof, p, m, WeakeningLeft.apply, pred )
        case WeakeningRight( p, m )            => handleWeakeningRule( proof, p, m, WeakeningRight.apply, pred )

        /* Logical rules */
        case AndRight( p1, a1, p2, a2 )        => handleBinaryRule( proof, p1, p2, a1, a2, AndRight.apply, pred )
        case OrLeft( p1, a1, p2, a2 )          => handleBinaryRule( proof, p1, p2, a1, a2, OrLeft.apply, pred )
        case ImpLeft( p1, a1, p2, a2 )         => handleBinaryRule( proof, p1, p2, a1, a2, ImpLeft.apply, pred )
        case NegLeft( p, a )                   => handleNegRule( proof, p, a, NegLeft.apply, pred )
        case NegRight( p, a )                  => handleNegRule( proof, p, a, NegRight.apply, pred )
        case OrRight( p, a1, a2 )              => handleUnaryRule( proof, p, a1, a2, OrRight.apply, pred )
        case AndLeft( p, a1, a2 )              => handleUnaryRule( proof, p, a1, a2, AndLeft.apply, pred )
        case ImpRight( p, a1, a2 )             => handleUnaryRule( proof, p, a1, a2, ImpRight.apply, pred )

        /* quantifier rules  */
        case AllRight( p, a, eigenv, qvar )    => handleStrongQuantRule( proof, p, a, AllRight.apply, pred )
        case ExLeft( p, a, eigenvar, qvar )    => handleStrongQuantRule( proof, p, a, ExLeft.apply, pred )
        case AllLeft( p, a, f, t )             => handleWeakQuantRule( proof, p, a, f, t, AllLeft.apply, pred )
        case ExRight( p, a, f, t )             => handleWeakQuantRule( proof, p, a, f, t, ExRight.apply, pred )

        //TODO: handle equality
        case Equality( p, e, a, flipped, pos ) => throw new Exception( "LKsk Equation not yet implemented." )

        case rule @ Cut( p1, a1, p2, a2 ) =>
          val main_is_cutanc = pred( rule.cutFormula )
          val new_cut_ancs_left = mapToUpperProof( proof.occConnectors( 0 ), cut_ancs, main_is_cutanc )
          val new_cut_ancs_right = mapToUpperProof( proof.occConnectors( 1 ), cut_ancs, main_is_cutanc )
          require( new_cut_ancs_left.size == p1.conclusion.size, "Cut ancestor information does not fit to end-sequent!" )
          require( new_cut_ancs_right.size == p2.conclusion.size, "Cut ancestor information does not fit to end-sequent!" )
          val s1 = apply( p1, new_cut_ancs_left, pred )
          val s2 = apply( p2, new_cut_ancs_right, pred )
          if ( main_is_cutanc ) {
            /* this cut is taken into account */
            handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs_left, new_cut_ancs_right )
          } else {
            //this one is skipped
            s1.foldLeft( Set.empty[( LKskProof, Sequent[Boolean] )] )( ( s, pm1 ) =>
              s ++ s2.map( pm2 => {
                val List( aux1, aux2 ) = pickrule( proof, List( p1, p2 ), List( pm1, pm2 ), List( a1, a2 ) )
                val rule = Cut( p1, castToSide( aux1 ), p2, castToSide( aux2 ) )
                val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), rule.occConnectors( 1 ), pm1, pm2, main_is_cutanc )
                ( rule, nca )
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

  /**
   * finds the cut ancestor sequent in the parent connected with the occurrence connector
   * @param connector
   * @param s
   * @return
   */
  def copySetToAncestor( connector: OccConnector[LabelledFormula], s: Sequent[Boolean] ) = {
    connector.parents( s ).map( _.head )
  }

  /**
   * finds the successor cut-ancestor sequent from one parent
   * @param connector connector from parent of pm._1 to pm._1
   * @param pm a pair proof + cut_ancestor sequent
   * @param default the default to take if a formula has no parent
   * @tparam T must be the same as the contents of the conclusion of pm._1
   * @return the cut ancestorship sequent for the parent of pm._1
   */
  def calculate_child_cut_ecs[T](
    connector: OccConnector[T],
    pm:        ( LKskProof, Sequent[Boolean] ),
    default:   Boolean
  ): Sequent[Boolean] = {
    //take over parent's cut ancestors in end-sequent,
    val nca: Sequent[Boolean] =
      pm._1.conclusion.indicesSequent.map( connector.parents( _ ) ).map( { case x if x.isEmpty => default; case x => pm._2( x.head ) } )
    nca
  }

  /**
   * finds the successor cut-ancestor sequent from two parents
   * @param connector1 connector from first parent of pm._1 to pm._1
   * @param pm1 a pair proof + cut_ancestor sequent
   * @param connector2 connector from second parent of pm._1 to pm._1
   * @param pm2 a pair proof + cut_ancestor sequent
   * @param default the default to take if a formula has no parent
   * @tparam T must be the same as the contents of the conclusion of pm1._1 and pm2._1
   * @return the cut ancestorship sequent for the parent of pm._1
   */
  def calculate_child_cut_ecs[T](
    connector1: OccConnector[T],
    connector2: OccConnector[T],
    pm1:        ( LKskProof, Sequent[Boolean] ),
    pm2:        ( LKskProof, Sequent[Boolean] ),
    default:    Boolean
  ): Sequent[Boolean] = {
    val nca1 = calculate_child_cut_ecs( connector1, pm1, default )
    val nca2 = calculate_child_cut_ecs( connector2, pm2, default )
    nca1.indicesSequent.map( x => nca1( x ) || nca2( x ) )
  }

  /* traces the ancestor relationship to infer cut-formulas in the parent proof. if a formula does not have parents,
     use default */
  private def mapToUpperProof[Formula]( conn: OccConnector[Formula], cut_occs: Sequent[Boolean], default: Boolean ) =
    conn.parents( cut_occs ).map( _.headOption getOrElse default )

  def handleBinaryESAnc[Side1 <: SequentIndex, Side2 <: SequentIndex]( proof: LKskProof, parent1: LKskProof, parent2: LKskProof,
                                                                       s1:          Set[( LKskProof, Sequent[Boolean] )],
                                                                       s2:          Set[( LKskProof, Sequent[Boolean] )],
                                                                       constructor: ( LKskProof, Side1, LKskProof, Side2 ) => LKskProof ) =
    s1.foldLeft( Set.empty[( LKskProof, Sequent[Boolean] )] )( ( s, p1 ) =>
      s ++ s2.map( p2 => {
        val List( a1, a2 ) = pickrule( proof, List( parent1, parent2 ), List( p1, p2 ), List( proof.auxIndices( 0 )( 0 ), proof.auxIndices( 1 )( 0 ) ) )
        val rule = constructor( p1._1, castToSide( a1 ), p2._1, castToSide( a2 ) )
        val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), rule.occConnectors( 1 ), p1, p2, false )
        ( rule, nca )
      } ) )

  def getESAncs( proof: LKskProof, cut_ancs: Sequent[Boolean] ): LabelledSequent = {
    //use cut_ancs as characteristic function to filter the the cut-ancestors from the current sequent
    ( proof.conclusion zip cut_ancs ).filterNot( _._2 ).map( _._1 )
  }

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKskProof, p1: LKskProof, p2: LKskProof,
                          s1: Set[( LKskProof, Sequent[Boolean] )], s2: Set[( LKskProof, Sequent[Boolean] )],
                          cut_ancs1: Sequent[Boolean], cut_ancs2: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs2 ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs1 ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  def weakenESAncs( esancs: LabelledSequent, s: Set[( LKskProof, Sequent[Boolean] )] ) = {
    val wl = s.map( p => esancs.antecedent.foldLeft( p )( ( p, fo ) => {
      val rule = WeakeningLeft( p._1, fo )
      val nca: Sequent[Boolean] = calculate_child_cut_ecs( rule.occConnectors( 0 ), p, false )
      ( rule, nca )
    } ) )
    wl.map( p => esancs.succedent.foldLeft( p )( ( p, fo ) => {
      val rule = WeakeningRight( p._1, fo )
      val nca: Sequent[Boolean] = calculate_child_cut_ecs( rule.occConnectors( 0 ), p, false )
      ( rule, nca )
    } ) )
  }

  def handleContractionRule[Side <: SequentIndex]( proof: LKskProof, p: LKskProof,
                                                   a1: SequentIndex, a2: SequentIndex,
                                                   constructor: ( LKskProof, Side, Side ) => LKskProof,
                                                   pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    val main_is_cutanc = cut_ancs( proof.mainIndices( 0 ) )
    if ( main_is_cutanc ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      val rp = constructor( pm._1, castToSide( a1_ ), castToSide( a2_ ) )
      val nca: Sequent[Boolean] = calculate_child_cut_ecs( rp.occConnectors( 0 ), pm, main_is_cutanc )
      ( rp, nca )
    } )
  }

  //implication does not weaken the second argument, we need two occs
  def handleUnaryRule[Side1 <: SequentIndex, Side2 <: SequentIndex]( proof: LKskProof, p: LKskProof, a1: Side1, a2: Side2,
                                                                     constructor: ( LKskProof, Side1, Side2 ) => LKskProof,
                                                                     pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      val rp = constructor( pm._1, castToSide( a1_ ), castToSide( a2_ ) )
      val conn = pm._1.occConnectors( 0 )
      val nca = pm._1.conclusion.indicesSequent.map( x => pm._2( conn.parent( x ) ) )
      ( rp, nca )
    } )
  }

  def handleWeakeningRule( proof: LKskProof, p: LKskProof, m: LabelledFormula,
                           constructor: ( LKskProof, LabelledFormula ) => LKskProof,
                           pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val maincutanc = cut_ancs( proof.mainIndices( 0 ) )
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val rule = constructor( pm._1, m )
      val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), pm, false )
      ( rule, nca )
    } )
  }

  def handleDefRule( proof: LKskProof, p: LKskProof, a: SequentIndex, f: HOLFormula,
                     constructor: ( LKskProof, SequentIndex, HOLFormula ) => LKskProof,
                     pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      val rule = constructor( pm._1, castToSide( a_ ), f )
      val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), pm, false )
      ( rule, nca )
    } )
  }

  def handleNegRule[Side <: SequentIndex]( proof: LKskProof, p: LKskProof, a: SequentIndex,
                                           constructor: ( LKskProof, Side ) => LKskProof,
                                           pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      val rule = constructor( pm._1, castToSide( a_ ) )
      val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), pm, false )
      ( rule, nca )
    } )
  }

  def handleWeakQuantRule[Side <: SequentIndex]( proof: LKskProof, p: LKskProof, a: Side, f: HOLFormula, t: LambdaExpression,
                                                 constructor: ( LKskProof, Side, HOLFormula, LambdaExpression ) => LKskProof,
                                                 pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      val rule = constructor( pm._1, castToSide( a_ ), f, t )
      val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), pm, false )
      ( rule, nca )
    } )
  }

  def handleStrongQuantRule[Side <: SequentIndex]( proof: LKskProof, p: LKskProof, a: Side,
                                                   constructor: ( LKskProof, Side, HOLFormula, Var ) => LKskProof,
                                                   pred:        HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else throw new Exception( "The proof is not skolemized!" )
  }

  def handleBinaryRule[Side1 <: SequentIndex, Side2 <: SequentIndex]( proof: LKskProof, p1: LKskProof, p2: LKskProof,
                                                                      a1: Side1, a2: Side2,
                                                                      constructor: ( LKskProof, Side1, LKskProof, Side2 ) => LKskProof,
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
                    pred: HOLFormula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[( LKskProof, Sequent[Boolean] )] = {
    val new_cut_ancs = copySetToAncestor( proof.occConnectors( 0 ), cut_ancs )
    val s1 = apply( p, new_cut_ancs, pred )
    ( cut_ancs( proof.mainIndices( 0 ) ), cut_ancs( proof.mainIndices( 1 ) ) ) match {
      case ( true, true ) =>
        s1
      case ( false, false ) =>
        s1 map ( pm => {
          val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( e, a ) )
          val rule = constructor( p, castToSide( a1_ ), castToSide( a2_ ), pos )
          val nca = calculate_child_cut_ecs( rule.occConnectors( 0 ), pm, false )
          ( rule, nca )
        } )

      case ( false, true ) =>
        //add equational axiom to the set
        val ef = p.formulas( e )
        val eflabel = p.labels( e )
        val aflabel = p.labels( a )
        val ax = Axiom( eflabel, aflabel, ef )
        val main_e = proof.mainIndices( 0 )
        val es = proof.conclusion.zipWithIndex.filter( x => x._2 != main_e && !cut_ancs( x._2 ) ).map( _._1 )
        val ca_sequent = Sequent( List( false ), List( true ) ) //TODO: check sequent
        val wax = weakenESAncs( es, Set( ( ax, ca_sequent ) ) )
        s1 ++ wax
      case ( true, false ) =>
        s1
    }
  }

  //pickrule returns a list of sequentIndices but the LKsk constructors need either Ant or Suc. Cast to appropriate.
  private def castToSide[Side <: SequentIndex]( si: SequentIndex ): Side =
    if ( si.isInstanceOf[Side] ) si.asInstanceOf[Side]
    else throw new Exception( s"The index $si is not on the expected side of the sequent!" )
}

