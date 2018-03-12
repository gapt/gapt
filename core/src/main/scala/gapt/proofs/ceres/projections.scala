/*
 * projections.scala
 *
 */

package gapt.proofs.ceres

import gapt.expr._
import gapt.proofs._
import gapt.proofs.ceres.Pickrule._
import gapt.proofs.lk._

object Projections {

  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKProof ): Set[LKProof] =
    apply( proof, proof.endSequent.map( _ => false ), x => true )

  def apply( proof: LKProof, pred: Formula => Boolean ): Set[LKProof] =
    apply( proof, proof.endSequent.map( _ => false ), pred )

  def apply( proof: LKProof, cut_ancs: Sequent[Boolean], pred: Formula => Boolean ): Set[LKProof] = {
    val rec = apply_( proof, cut_ancs, pred )
    /*
    val esanc = proof.endSequent.zipWithIndex.filterNot( x => cut_ancs( x._2 ) ).map( _._1 )
    val cutanc_new = rec.map( _.endSequent )
    //    println(s"esanc: $esanc")
    println( "start " + proof.getClass )
    if ( proof.mainIndices.size > 0 ) {
      cut_ancs( proof.mainIndices( 0 ) ) match {
        case true  => println( "Working on a cut-ancestor!" )
        case false => println( "Working on a es-ancestor!" )
      }
    } else {
      println( "No main formulas!" )
    }
    println( " es    " + proof.endSequent )
    println( " esanc " + esanc )
    cutanc_new.map( println )
    println( "end\n" )
    */
    rec
  }

  def apply_( proof: LKProof, cut_ancs: Sequent[Boolean], pred: Formula => Boolean ): Set[LKProof] = {
    implicit val c_ancs = cut_ancs
    //proof.occConnectors

    proof match {
      /* Structural rules except cut */
      case InitialSequent( _ )                    => Set( proof )

      case ContractionLeftRule( p, a1, a2 )       => handleContractionRule( proof, p, a1, a2, ContractionLeftRule.apply, pred )
      case ContractionRightRule( p, a1, a2 )      => handleContractionRule( proof, p, a1, a2, ContractionRightRule.apply, pred )
      case WeakeningLeftRule( p, m )              => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply, pred )
      case WeakeningRightRule( p, m )             => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply, pred )

      /* Logical rules */
      case AndRightRule( p1, a1, p2, a2 )         => handleBinaryRule( proof, p1, p2, a1, a2, AndRightRule.apply, pred )
      case OrLeftRule( p1, a1, p2, a2 )           => handleBinaryRule( proof, p1, p2, a1, a2, OrLeftRule.apply, pred )
      case ImpLeftRule( p1, a1, p2, a2 )          => handleBinaryRule( proof, p1, p2, a1, a2, ImpLeftRule.apply, pred )
      case NegLeftRule( p, a )                    => handleNegRule( proof, p, a, NegLeftRule.apply, pred )
      case NegRightRule( p, a )                   => handleNegRule( proof, p, a, NegRightRule.apply, pred )
      case OrRightRule( p, a1, a2 )               => handleUnaryRule( proof, p, a1, a2, OrRightRule.apply, pred )
      case AndLeftRule( p, a1, a2 )               => handleUnaryRule( proof, p, a1, a2, AndLeftRule.apply, pred )
      case ImpRightRule( p, a1, a2 )              => handleUnaryRule( proof, p, a1, a2, ImpRightRule.apply, pred )

      /* quantifier rules  */
      case ForallRightRule( p, a, eigenv, qvar )  => handleStrongQuantRule( proof, p, ForallRightRule.apply, pred )
      case ExistsLeftRule( p, a, eigenvar, qvar ) => handleStrongQuantRule( proof, p, ExistsLeftRule.apply, pred )
      case ForallLeftRule( p, a, f, t, v )        => handleWeakQuantRule( proof, p, a, f, t, v, ForallLeftRule.apply, pred )
      case ExistsRightRule( p, a, f, t, v )       => handleWeakQuantRule( proof, p, a, f, t, v, ExistsRightRule.apply, pred )
      case ForallSkRightRule( p, a, m, t, d )     => handleSkQuantRule( proof, p, a, m, t, d, ForallSkRightRule.apply, pred )
      case ExistsSkLeftRule( p, a, m, t, d )      => handleSkQuantRule( proof, p, a, m, t, d, ExistsSkLeftRule.apply, pred )

      case DefinitionLeftRule( p, a, m )          => handleDefRule( proof, p, a, m, DefinitionLeftRule.apply, pred )
      case DefinitionRightRule( p, a, m )         => handleDefRule( proof, p, a, m, DefinitionRightRule.apply, pred )
      case EqualityLeftRule( p1, e, a, con )      => handleEqRule( proof, p1, e, a, con, EqualityLeftRule.apply, pred )
      case EqualityRightRule( p1, e, a, con )     => handleEqRule( proof, p1, e, a, con, EqualityRightRule.apply, pred )
      case rule @ CutRule( p1, a1, p2, a2 ) =>
        if ( pred( rule.cutFormula ) ) {
          /* this cut is taken into account */
          val new_cut_ancs_left = mapToUpperProof( proof.occConnectors( 0 ), cut_ancs, default = true )
          val new_cut_ancs_right = mapToUpperProof( proof.occConnectors( 1 ), cut_ancs, default = true )
          require( new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
          require( new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
          val s1 = apply( p1, new_cut_ancs_left, pred )
          val s2 = apply( p2, new_cut_ancs_right, pred )
          handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs_left, new_cut_ancs_right )
        } else {
          /* this cut is skipped */
          //println( "SKIPPING CUT" )
          val new_cut_ancs_left = mapToUpperProof( proof.occConnectors( 0 ), cut_ancs, default = false )
          val new_cut_ancs_right = mapToUpperProof( proof.occConnectors( 1 ), cut_ancs, default = false )
          require( new_cut_ancs_left.size == p1.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
          require( new_cut_ancs_right.size == p2.endSequent.size, "Cut ancestor information does not fit to end-sequent!" )
          val s1 = apply( p1, new_cut_ancs_left, pred )
          val s2 = apply( p2, new_cut_ancs_right, pred )
          s1.foldLeft( Set.empty[LKProof] )( ( s, pm1 ) =>
            s ++ s2.map( pm2 => {
              require( p1.conclusion( a1 ) == p2.conclusion( a2 ), "Original cut formulas must be equal!" )
              val List( aux1, aux2 ) = pickrule( proof, List( p1, p2 ), List( pm1, pm2 ), List( a1, a2 ) )
              require( pm1.conclusion( aux1 ) == pm2.conclusion( aux2 ), "New cut formulas must be equal!" )
              CutRule( pm1, aux1, pm2, aux2 )
            } ) )
        }
    }
  }

  /* finds the cut ancestor sequent in the parent connected with the occurrence connector */
  def copySetToAncestor( connector: SequentConnector, s: Sequent[Boolean] ) = {
    connector.parents( s ).map( _.head )
  }

  /* traces the ancestor relationship to infer cut-formulas in the parent proof. if a formula does not have parents,
     use default */
  private def mapToUpperProof[Formula]( conn: SequentConnector, cut_occs: Sequent[Boolean], default: Boolean ) =
    conn.parents( cut_occs ).map( _.headOption getOrElse default )

  def handleBinaryESAnc( proof: LKProof, parent1: LKProof, parent2: LKProof, s1: Set[LKProof], s2: Set[LKProof],
                         constructor: ( LKProof, SequentIndex, LKProof, SequentIndex ) => LKProof ) =
    s1.foldLeft( Set.empty[LKProof] )( ( s, p1 ) =>
      s ++ s2.map( p2 => {
        val List( a1, a2 ) = pickrule( proof, List( parent1, parent2 ), List( p1, p2 ), List( proof.auxIndices( 0 )( 0 ), proof.auxIndices( 1 )( 0 ) ) )
        constructor( p1, a1, p2, a2 )
      } ) )

  def getESAncs( proof: LKProof, cut_ancs: Sequent[Boolean] ): HOLSequent =
    //use cut_ancs as characteristic function to filter the the cut-ancestors from the current sequent
    ( proof.endSequent zip cut_ancs ).filterNot( _._2 ).map( _._1 )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof,
                          s1: Set[LKProof], s2: Set[LKProof],
                          cut_ancs1: Sequent[Boolean], cut_ancs2: Sequent[Boolean] ): Set[LKProof] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs2 ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs1 ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  //TODO: this a duplication of some function lk
  def weakenESAncs( esancs: HOLSequent, s: Set[LKProof] ) = {
    val wl = s.map( p => esancs.antecedent.foldLeft( p )( ( p, fo ) => WeakeningLeftRule( p, fo ) ) )
    wl.map( p => esancs.succedent.foldLeft( p )( ( p, fo ) => WeakeningRightRule( p, fo ) ) )
  }

  def handleContractionRule( proof: LKProof, p: LKProof,
                             a1: SequentIndex, a2: SequentIndex,
                             constructor: ( LKProof, SequentIndex, SequentIndex ) => LKProof,
                             pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      constructor( pm, a1_, a2_ )
    } )
  }

  //implication does not weaken the second argument, we need two occs
  def handleUnaryRule[T]( proof: LKProof, p: LKProof, a1: SequentIndex, a2: SequentIndex,
                          constructor: ( LKProof, SequentIndex, SequentIndex ) => LKProof,
                          pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( a1, a2 ) )
      constructor( pm, a1_, a2_ )
    } )
  }

  def handleWeakeningRule( proof: LKProof, p: LKProof, m: Formula,
                           constructor: ( LKProof, Formula ) => LKProof,
                           pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => constructor( pm, m ) )
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: SequentIndex, m: Formula,
                     constructor: ( LKProof, SequentIndex, Formula ) => LKProof,
                     pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_, m )
    } )
  }

  def handleNegRule( proof: LKProof, p: LKProof, a: SequentIndex,
                     constructor: ( LKProof, SequentIndex ) => LKProof,
                     pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_ )
    } )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: SequentIndex, f: Formula, t: Expr, qvar: Var,
                           constructor: ( LKProof, SequentIndex, Formula, Expr, Var ) => LKProof,
                           pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_, f, t, qvar )
    } )
  }

  def handleSkQuantRule( proof: LKProof, p: LKProof, a: SequentIndex, m: Formula, t: Expr, d: Expr,
                         constructor: ( LKProof, SequentIndex, Formula, Expr, Expr ) => LKProof,
                         pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else s.map( pm => {
      val List( a_ ) = pickrule( proof, List( p ), List( pm ), List( a ) )
      constructor( pm, a_, m, t, d )
    } )
  }

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: SequentIndex, a2: SequentIndex,
                        constructor: ( LKProof, SequentIndex, LKProof, SequentIndex ) => LKProof,
                        pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ) = {
    val new_cut_ancs1 = copySetToAncestor( proof.occConnectors( 0 ), cut_ancs )
    val new_cut_ancs2 = copySetToAncestor( proof.occConnectors( 1 ), cut_ancs )
    val s1 = apply( p1, new_cut_ancs1, pred )
    val s2 = apply( p2, new_cut_ancs2, pred )
    // private val nLine = sys.props("line.separator")
    //println("Binary rule on:"+nLine+s1.map(_.root)+nLine+s2.map(_.root))
    if ( cut_ancs( proof.mainIndices( 0 ) ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs1, new_cut_ancs2 )
    else
      handleBinaryESAnc( proof, p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKProof, p: LKProof, e: SequentIndex, a: SequentIndex,
                    con: Abs, constructor: ( LKProof, SequentIndex, SequentIndex, Abs ) => LKProof,
                    pred: Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val new_cut_ancs = copySetToAncestor( proof.occConnectors( 0 ), cut_ancs )
    val s1 = apply( p, new_cut_ancs, pred )
    /* distinguish on the cut-ancestorship of the equation (left component) and of the auxiliary formula (right component)
       since the rule does not give direct access to the occurence of e in the conclusion, we look at the premise
     */
    val e_idx_conclusion = proof.occConnectors( 0 ).child( e )
    //    require( cut_ancs( e_idx_conclusion ) == true, "This is not a proof from the old calculus!" )
    val aux_ca = cut_ancs( proof.mainIndices( 0 ) )
    val eq_ca = cut_ancs( e_idx_conclusion )
    val mainf = proof.endSequent( proof.mainIndices( 0 ) )
    val eqf = proof.endSequent( e_idx_conclusion )
    //println( s"main formula: $mainf $aux_ca eq: $eqf $eq_ca" )
    ( aux_ca, eq_ca ) match {
      case ( true, true ) =>
        //println( "eq t t" )
        s1
      case ( true, false ) =>
        //println( "eq t f" )
        val ef = p.endSequent( e )
        val ax = LogicalAxiom( ef )
        val main_e = proof.mainIndices( 0 )
        val es = proof.endSequent.zipWithIndex.filter( x => x._2 != main_e &&
          x._2 != e_idx_conclusion &&
          !cut_ancs( x._2 ) ).map( _._1 )
        val wax = weakenESAncs( es, Set( ax ) )
        s1 ++ wax
      case ( false, true ) =>
        //println( "eq f t" )
        s1 map ( pm => {
          //println( p.endSequent( e ) )
          //we first pick our aux formula
          val candidates = a match {
            case Ant( _ ) => pm.endSequent.zipWithIndex.antecedent
            case Suc( _ ) => pm.endSequent.zipWithIndex.succedent
          }
          val aux = pick( p, a, candidates )
          //then add the weakening
          //println( "weakening: " + p.endSequent( e ) )
          val wproof = WeakeningLeftRule( pm, p.endSequent( e ) )
          //trace the aux formulas to the new rule
          val conn = wproof.occConnectors( 0 )
          val waux = conn.child( aux )
          val weq = wproof.mainIndices( 0 )
          require( waux != weq, "Aux formulas must be different!" )
          //and apply it
          val rule = constructor( wproof, weq, waux, con )
          rule
        } )
      case ( false, false ) =>
        //println( "eq f f" )
        s1 map ( pm => {
          //println( p.endSequent( e ) )
          val List( a1_, a2_ ) = pickrule( proof, List( p ), List( pm ), List( e, a ) )
          constructor( pm, a1_, a2_, con )
        } )

    }
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof,
                             constructor: ( LKProof, SequentIndex, Var, Var ) => LKProof,
                             pred:        Formula => Boolean )( implicit cut_ancs: Sequent[Boolean] ): Set[LKProof] = {
    val s = apply( p, copySetToAncestor( proof.occConnectors( 0 ), cut_ancs ), pred )
    if ( cut_ancs( proof.mainIndices( 0 ) ) ) s
    else throw new Exception( "The proof is not skolemized!" )
  }
}

