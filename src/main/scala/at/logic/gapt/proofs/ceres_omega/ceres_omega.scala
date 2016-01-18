package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr.hol.{ freeHOVariables, containsQuantifierOnLogicalLevel }
import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.utils.dssupport.ListSupport._
import at.logic.gapt.proofs.{ SequentIndex, Suc, Ant, Sequent }
import at.logic.gapt.proofs.ral._
import at.logic.gapt.utils.logging.Logger

/**
 * Created by marty on 10/6/14.
 */
object ceres_omega extends ceres_omega

class ceres_omega extends Logger {
  //TODO: check if we cant replace it with the CERES.skip_propositional method
  def skip_propositional( x: HOLFormula ) = containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty

  val nLine = sys.props( "line.separator" )

  /* Bug: Like the old versiom this code assumes that we can delete the labels while constructing the proof, not only at
     the cut. Because of that, we might contract the wrong formulas. If the Ral proof comes from a first-order import,
     it does not matter. A CNF or skolemization step introduced at a leaf might not be applicable if we trace the wrong
     introducing axiom. So far these steps are not yet implemented, so it's not such a problem.
    */
  //TODO: fix this bug

  /**
   * Applies the CERES_omega method to a proof.
   * @param projections This is the set of projections to use. A projection to reflexvity is generated if needed.
   * @param ralproof The R_al proof to use as skeleton.
   * @param es The end-sequent of the original proof.
   * @param struct The struct of the original proof. (unused at the moment)
   * @return a pair of an LKProof with atomic cuts only and of the subsequent of its root which corresponds the Ral sequent
   */
  def apply(
    projections: Set[( LKskProof, Sequent[Boolean] )],
    ralproof:    RalProof,
    es:          LabelledSequent,
    struct:      Struct[Label]
  ): ( LKskProof, Sequent[Boolean] ) = {
    val r = ralproof match {
      //reflexivity as initial rule
      case RalInitial( Sequent( Seq(), Seq( ( label, equation @ Eq( x, y ) ) ) ) ) if ( x == y ) && ( x.exptype == Ti ) =>
        Projections.reflexivity_projection( es, x, label )

      case RalInitial( root ) =>
        val candidates = projections.toList.flatMap( x => {
          val pes = filterEndsequent( x._1.conclusion, x._2 )
          StillmanSubsumptionAlgorithmHOL.subsumes_by( pes.map( _._2 ), root.map( _._2 ) ) match {
            case None        => Nil
            case Some( sub ) => List( ( x, sub ) )
          }
        } )

        candidates match {
          case ( ( proof, cut_anc ), sub ) :: _ =>
            val subproof = applySubstitution( sub )( proof )
            val clause = filterEndsequent( subproof.conclusion, cut_anc )
            //subsumption has an implicit contraction. we first find out, which formulas are superfluous...
            val tocontract = Sequent[LabelledFormula](
              diffModuloOccurrence( clause.antecedent, root.antecedent ),
              diffModuloOccurrence( clause.succedent, root.succedent )
            )
            // and contract two equal formulas which are cut ancestors (i.e. not part of the final end-sequent)
            val acontr = tocontract.antecedent.foldLeft( ( subproof, cut_anc ) )( ( pair, occ ) => {
              val ( p, ca ) = pair
              p.conclusion.zipWithIndex.antecedent.find( x => x._1 == occ && ca( x._2 ) ) match {
                case Some( ( _, idx1 @ Ant( _ ) ) ) =>
                  p.conclusion.zipWithIndex.antecedent.find( x => x._1 == occ && x._2 != idx1 && ca( x._2 ) ) match {
                    case Some( ( _, idx2 @ Ant( _ ) ) ) =>
                      val rule = ContractionLeft( p, idx1, idx2 )
                      val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), pair, false )
                      ( rule, nca )
                    case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
                  }
                case _ => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
              }
            } )
            val scontr = tocontract.succedent.foldLeft( acontr )( ( pair, occ ) => {
              val ( p, ca ) = pair
              p.conclusion.zipWithIndex.succedent.find( x => x._1 == occ && ca( x._2 ) ) match {
                case Some( ( _, idx1 @ Suc( _ ) ) ) =>
                  p.conclusion.zipWithIndex.succedent.find( x => x._1 == occ && x._2 != idx1 && ca( x._2 ) ) match {
                    case Some( ( _, idx2 @ Suc( _ ) ) ) =>
                      val rule = ContractionRight( p, idx1, idx2 )
                      val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), pair, false )
                      ( rule, nca )
                    case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
                  }
                case _ => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
              }
            } )
            scontr
          case Nil =>
            throw new Exception( "Could not find a projection for the clause " + root + " in " +
              projections.map( x => filterEndsequent( x._1.conclusion, x._2 ) ).mkString( nLine ) )
        }

      case cut @ RalCut( parent1, p1occs, parent2, p2occs ) =>
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        //since we automatically delete the labels on the cut-ancestors, we need to look for an unlabeled cut_anc occurrence
        val cut_lformula: LabelledFormula = ( Seq(), cut.cutFormula )
        val cleft = p1occs.tail.foldLeft( ( lkparent1, ca1 ) )( ( pair, _ ) => {
          val ( proof, ca ) = pair
          val a1 = findAuxInSuccedent( cut_lformula, proof.conclusion, Seq(), ca )
          val a2 = findAuxInSuccedent( cut_lformula, proof.conclusion, Seq( a1 ), ca )
          val rule = ContractionRight( proof, a1, a2 )
          val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), pair, false )
          ( rule, nca )
        } )
        val cright = p2occs.tail.foldLeft( ( lkparent2, ca2 ) )( ( pair, _ ) => {
          val ( proof, ca ) = pair
          val a1 = findAuxInAntecedent( cut_lformula, proof.conclusion, Seq(), ca )
          val a2 = findAuxInAntecedent( cut_lformula, proof.conclusion, Seq( a1 ), ca )
          val rule = ContractionLeft( proof, a1, a2 )
          val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), pair, false )
          ( rule, nca )
        } )

        val cutfleft = findAuxInSuccedent( cut_lformula, cleft._1.conclusion, Seq(), cleft._2 )
        val cutfright = findAuxInAntecedent( cut_lformula, cright._1.conclusion, Seq(), cright._2 )

        val rule = Cut( cleft._1, cutfleft, cright._1, cutfright )
        val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), rule.occConnectors( 1 ), cleft, cright, false )
        contractEndsequent( ( rule, nca ), es )

      case RalFactor( parent, contr @ Ant( _ ), aux ) =>
        val clformula = ralproof.conclusion( contr )

        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )

        val c1 = findAuxInAntecedent( clformula, lkparent.conclusion, Seq(), ca )
        val c2 = findAuxInAntecedent( clformula, lkparent.conclusion, Seq( c1 ), ca )
        val rule = ContractionLeft( lkparent, c1, c2 )
        val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( lkparent, ca ), false )
        ( rule, nca )

      case RalFactor( parent, contr @ Suc( _ ), aux ) =>
        val clformula = ralproof.conclusion( contr )

        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )

        val c1 = findAuxInSuccedent( clformula, lkparent.conclusion, Seq(), ca )
        val c2 = findAuxInSuccedent( clformula, lkparent.conclusion, Seq( c1 ), ca )
        val rule = ContractionRight( lkparent, c1, c2 )
        val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( lkparent, ca ), false )
        ( rule, nca )

      case RalPara( _, _, _, _, pos, _ ) if pos.size != 1 =>
        throw new Exception( "Paramodulations at multiple positions are not handled!" )

      case RalPara( parent1, eqocc, parent2, p2occ @ Ant( _ ), Seq( pos ), flipped ) =>
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        val eqlformula = parent1.conclusion( eqocc )

        def fa( boolseq: Sequent[Boolean] ) = findAuxOptionInAntecedent( eqlformula, lkparent2.conclusion, Seq(), boolseq )
        def fs( boolseq: Sequent[Boolean] ) = findAuxOptionInSuccedent( eqlformula, lkparent1.conclusion, Seq(), boolseq )

        // check if the eqformula is already in the antecedent of parent 2. if yes, use the unary rule, if not simulate the binary rule
        ( fa( lkparent2.conclusion.map( _ => true ) ), fs( ca1 ) ) match {
          case ( Some( eqidx ), _ ) if parent1.formulas( eqocc ) != parent2.formulas( p2occ ) => //need to exclude paramodulation into the same equation
            val modulant = findAuxInAntecedent( parent2.conclusion( p2occ ), lkparent2.conclusion, Seq( eqidx ), ca2 )
            val rule = Equality( lkparent2, eqidx, modulant, flipped, Seq( pos ) )
            val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( lkparent2, ca2 ), false )
            ( rule, nca )
          case ( _, Some( eqidx ) ) =>
            val wlkparent2 = WeakeningLeft( lkparent2, lkparent1.conclusion( eqidx ) )
            val nca = Projections.calculate_child_cut_ecs( wlkparent2, wlkparent2.occConnectors( 0 ), ( lkparent2, ca2 ), true )
            val modulant = findAuxInAntecedent( parent2.conclusion( p2occ ), wlkparent2.conclusion, Seq( eqidx ), nca )
            val weqidx = wlkparent2.mainIndices( 0 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of WeakeningLeft!" )
            }
            val rule = Equality( wlkparent2, weqidx, modulant, flipped, Seq( pos ) )
            val nc2 = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( wlkparent2, nca ), false )
            val ruleeqidx = rule.occConnectors( 0 ).child( weqidx ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of Equation (left)!" )
            }
            val cutrule = Cut( lkparent1, eqidx, rule, ruleeqidx )
            val cnca = Projections.calculate_child_cut_ecs( cutrule, cutrule.occConnectors( 0 ), cutrule.occConnectors( 1 ),
              ( lkparent1, ca1 ), ( rule, nc2 ), false )

            contractEndsequent( ( cutrule, cnca ), es )
          case ( None, None ) =>
            throw new Exception( s"Could not find equation $eqlformula in parents ${lkparent1.conclusion} or ${lkparent2.conclusion}!" )
        }

      case RalPara( parent1, eqocc, parent2, p2occ @ Suc( _ ), Seq( pos ), flipped ) =>
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        val eqlformula = parent1.conclusion( eqocc )

        def fa( boolseq: Sequent[Boolean] ) = findAuxOptionInAntecedent( eqlformula, lkparent2.conclusion, Seq(), boolseq )
        def fs( boolseq: Sequent[Boolean] ) = findAuxOptionInSuccedent( eqlformula, lkparent1.conclusion, Seq(), boolseq )

        // check if the eqformula is already in the antecedent of parent 2. if yes, use the unary rule, if not simulate the binary rule
        ( fa( lkparent2.conclusion.map( _ => true ) ), fs( ca1 ) ) match {
          case ( Some( eqidx ), _ ) =>
            val modulant = findAuxInSuccedent( parent2.conclusion( p2occ ), lkparent2.conclusion, Seq( eqidx ), ca2 )
            val rule = Equality( lkparent2, eqidx, modulant, flipped, Seq( pos ) )
            val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( lkparent2, ca2 ), false )
            ( rule, nca )
          case ( _, Some( eqidx ) ) =>
            //weaken equation on left hand side of lk parent 2, calculate new cut-ancestors
            val wlkparent2 = WeakeningLeft( lkparent2, lkparent1.conclusion( eqidx ) )
            val nca = Projections.calculate_child_cut_ecs( wlkparent2, wlkparent2.occConnectors( 0 ), ( lkparent2, ca2 ), true )
            //find indices of modulant formula and equation in the new inference
            val modulant = findAuxInSuccedent( parent2.conclusion( p2occ ), wlkparent2.conclusion, Seq(), nca )
            val weqidx = wlkparent2.mainIndices( 0 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of WeakeningLeft!" )
            }

            val rule = Equality( wlkparent2, weqidx, modulant, flipped, Seq( pos ) )
            val nc2 = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), ( wlkparent2, nca ), false )
            val ruleeqidx = rule.occConnectors( 0 ).child( weqidx ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of Equation (left)!" )
            }
            val cutrule = Cut( lkparent1, eqidx, rule, ruleeqidx )
            val cnca = Projections.calculate_child_cut_ecs( cutrule, cutrule.occConnectors( 0 ), cutrule.occConnectors( 1 ),
              ( lkparent1, ca1 ), ( rule, nc2 ), false )

            contractEndsequent( ( cutrule, cnca ), es )
          case ( None, None ) =>
            throw new Exception( s"Could not find equation $eqlformula!" )
        }

      case RalSub( parent, sub ) =>
        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )
        val rule = applySubstitution( sub )( lkparent )
        //we use the invariant that the order of formula occurrences does not change by applying the substitution
        ( rule, ca )

      case _ => throw new Exception( "Unhandled case: " + ralproof )
    }
    debug( s"${ralproof.longName}" )
    debug( s"cutanc ${r._1.conclusion.zipWithIndex.filter( x => r._2( x._2 ) ).map( _._1._2 )}" )
    r
  }

  def findAuxOptionInAntecedent( aux: LabelledFormula, sequent: LabelledSequent,
                                 exclusion_list: Seq[SequentIndex], bool_filter: Sequent[Boolean] ): Option[Ant] =
    sequent.zipWithIndex.antecedent.find( x => x._1 == aux && !exclusion_list.contains( x._2 ) && bool_filter( x._2 ) ) match {
      case Some( ( _, x @ Ant( _ ) ) ) => Some( x )
      case None                        => None
    }

  def findAuxInAntecedent( aux: LabelledFormula, sequent: LabelledSequent,
                           exclusion_list: Seq[SequentIndex], bool_filter: Sequent[Boolean] ): Ant =
    findAuxOptionInAntecedent( aux, sequent, exclusion_list, bool_filter ).getOrElse(
      throw new Exception( s"Could not find the auxiliary formula $aux in antecedent of $sequent with exclusion list $exclusion_list and filter $bool_filter" )
    )

  def findAuxOptionInSuccedent( aux: LabelledFormula, sequent: LabelledSequent,
                                exclusion_list: Seq[SequentIndex], bool_filter: Sequent[Boolean] ): Option[Suc] =
    sequent.zipWithIndex.succedent.find( x => x._1 == aux && !exclusion_list.contains( x._2 ) && bool_filter( x._2 ) ) match {
      case Some( ( _, x @ Suc( _ ) ) ) => Some( x )
      case None                        => None
    }

  def findAuxInSuccedent( aux: LabelledFormula, sequent: LabelledSequent,
                          exclusion_list: Seq[SequentIndex], bool_filter: Sequent[Boolean] ): Suc =
    findAuxOptionInSuccedent( aux, sequent, exclusion_list, bool_filter ).getOrElse(
      throw new Exception( s"Could not find the auxiliary formula $aux in succedent of $sequent with exclusion list $exclusion_list and filter $bool_filter" )
    )

  /**
   * After an application of a binary rule, end-sequent material might be duplicated. This method adds contractions
   * for every end-sequent formula.
   * @param p a proof with an end-sequent of the form: es x es x C (where C is some additional content)
   * @param es the end-sequent material which occurs twice
   * @return a proof with an end-sequent of the form: es x C
   */
  def contractEndsequent( p: ( LKskProof, Sequent[Boolean] ), es: LabelledSequent ): ( LKskProof, Sequent[Boolean] ) = {
    val contr_left = es.antecedent.foldLeft( p )( ( rp, fo ) => {
      val ( proof, ca ) = rp
      val esa = invert( ca )
      val a1 = findAuxInAntecedent( fo, proof.conclusion, Seq(), esa )
      val a2 = findAuxInAntecedent( fo, proof.conclusion, Seq( a1 ), esa )
      val rule = ContractionLeft( proof, a1, a2 )
      val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), rp, false )
      ( rule, nca )
    } )
    val contr_right = es.succedent.foldLeft( p )( ( rp, fo ) => {
      val ( proof, ca ) = rp
      val esa = invert( ca )
      val a1 = findAuxInSuccedent( fo, proof.conclusion, Seq(), esa )
      val a2 = findAuxInSuccedent( fo, proof.conclusion, Seq( a1 ), esa )
      val rule = ContractionRight( proof, a1, a2 )
      val nca = Projections.calculate_child_cut_ecs( rule, rule.occConnectors( 0 ), rp, false )
      ( rule, nca )
    } )
    contr_right
  }

  /* inverts a boolean sequent */
  def invert( s: Sequent[Boolean] ) = s.map( !_ )

  /* removes the final end-sequent from a projection's current end-sequent */
  def filterEndsequent( root: LabelledSequent, cut_anc: Sequent[Boolean] ) =
    root.zipWithIndex.filter( x => cut_anc( x._2 ) ).map( _._1 )

  def diffModuloOccurrence( from: Seq[LabelledFormula], what: Seq[( RalProof.Label, HOLFormula )] ) = {
    what.foldLeft( from.toList )( ( l, occ ) =>
      removeFirstWhere( l, ( x: LabelledFormula ) => x._1 == occ._1 && x._2 == occ._2 ) )
  }

}
