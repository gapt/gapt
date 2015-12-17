package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.utils.dssupport.ListSupport._
import at.logic.gapt.proofs.{ SequentIndex, Suc, Ant, Sequent }
import at.logic.gapt.proofs.ral._

//this is a dummy until apply subst is done
object applySubstitution {
  def apply( proof: LKskProof, subst: Substitution ): ( LKskProof, Map[SequentIndex, SequentIndex] ) = {
    //TODO: implement
    ( proof, Map() )
  }
}

/**
 * Created by marty on 10/6/14.
 */
object ceres_omega extends ceres_omega

class ceres_omega {

  val nLine = sys.props( "line.separator" )

  private def check_es( s: LabelledSequent, c: LabelledSequent, es: LabelledSequent ): LabelledSequent = {

    s
  }

  private def invert( s: Sequent[Boolean] ) = s.map( !_ )

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
  ): ( LKskProof, Sequent[Boolean] ) =
    ralproof match {
      //reflexivity as initial rule
      case RalInitial( Sequent( Seq(), Seq( ( label, equation @ Eq( x, y ) ) ) ) ) if ( x == y ) && ( x.exptype == Ti ) =>

        Projections.reflexivity_projection( es, Ti, label )

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
            val subproof = applySubstitution( proof, sub )._1
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
                      val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), pair, false )
                      ( rule, nca )
                    case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
                  }
                case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
              }
            } )
            val scontr = tocontract.succedent.foldLeft( acontr )( ( pair, occ ) => {
              val ( p, ca ) = pair
              p.conclusion.zipWithIndex.succedent.find( x => x._1 == occ && ca( x._2 ) ) match {
                case Some( ( _, idx1 @ Suc( _ ) ) ) =>
                  p.conclusion.zipWithIndex.succedent.find( x => x._1 == occ && x._2 != idx1 && ca( x._2 ) ) match {
                    case Some( ( _, idx2 @ Suc( _ ) ) ) =>
                      val rule = ContractionRight( p, idx1, idx2 )
                      val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), pair, false )
                      ( rule, nca )
                    case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
                  }
                case None => throw new Exception( "Could not find an element to contract for " + occ + " in " + root )
              }
            } )

            //          require( scontr.root.toHOLSequent.multiSetEquals( ( nclause compose es ).toHOLSequent ), "The root " + f( scontr.root ) + " must consist of the clause " + f( nclause ) + " plus the end-sequent " + f( es ) )
            //          require( scontr.root.occurrences.size == es.occurrences.size + nclause.occurrences.size, "The size of the generated end-sequent " + root + " is not the size of the end-sequent " + f( es ) + " + the size of the clause " + nclause )

            //          require( ( nclause.occurrences diff scontr.root.occurrences ).isEmpty )
            scontr
          case Nil =>
            throw new Exception( "Could not find a projection for the clause " + root + " in " +
              projections.map( x => filterEndsequent( x._1.conclusion, x._2 ) ).mkString( nLine ) )
        }

      case cut @ RalCut( parent1, p1occs, parent2, p2occs ) =>
        val root = ralproof.formulas
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        //since we automatically delete the labels on the cut-ancestors, we need to look for an onlabeled cut_anc occurence
        val cut_lformula: LabelledFormula = ( Seq(), cut.cutFormula )
        val cleft = p1occs.foldLeft( ( lkparent1, ca1 ) )( ( pair, _ ) => {
          val ( proof, ca ) = pair
          val a1 = findAuxInSuccedent( cut_lformula, proof.conclusion, Seq(), ca )
          val a2 = findAuxInSuccedent( cut_lformula, proof.conclusion, Seq( a1 ), ca )
          val rule = ContractionRight( proof, a1, a2 )
          val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), pair, false )
          ( rule, nca )
        } )
        val cright = p2occs.foldLeft( ( lkparent2, ca2 ) )( ( pair, _ ) => {
          val ( proof, ca ) = pair
          val a1 = findAuxInAntecedent( cut_lformula, proof.conclusion, Seq(), ca )
          val a2 = findAuxInAntecedent( cut_lformula, proof.conclusion, Seq( a1 ), ca )
          val rule = ContractionLeft( proof, a1, a2 )
          val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), pair, false )
          ( rule, nca )
        } )

        val cutfleft = findAuxInSuccedent( cut_lformula, cleft._1.conclusion, Seq(), cleft._2 )
        val cutfright = findAuxInAntecedent( cut_lformula, cright._1.conclusion, Seq(), cright._2 )

        val rule = Cut( cleft._1, cutfleft, cright._1, cutfright )
        val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), rule.occConnectors( 1 ), cleft, cright, false )
        contractEndsequent( ( rule, nca ), es )

      case RalFactor( parent, contr @ Ant( _ ), aux ) =>
        val root = ralproof.formulas
        val clformula = ralproof.conclusion( contr )

        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )

        val c1 = findAuxInAntecedent( clformula, lkparent.conclusion, Seq(), ca )
        val c2 = findAuxInAntecedent( clformula, lkparent.conclusion, Seq( c1 ), ca )
        val rule = ContractionLeft( lkparent, c1, c2 )
        val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( lkparent, ca ), false )
        ( rule, nca )

      case RalFactor( parent, contr @ Suc( _ ), aux ) =>
        val root = ralproof.formulas
        val clformula = ralproof.conclusion( contr )

        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )

        val c1 = findAuxInSuccedent( clformula, lkparent.conclusion, Seq(), ca )
        val c2 = findAuxInSuccedent( clformula, lkparent.conclusion, Seq( c1 ), ca )
        val rule = ContractionRight( lkparent, c1, c2 )
        val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( lkparent, ca ), false )
        ( rule, nca )

      case RalPara( _, _, _, _, pos, _ ) if pos.size != 1 =>
        throw new Exception( "Paramodulations at multiple positions are not handled!" )

      case RalPara( parent1, p1occ, parent2, p2occ @ Ant( _ ), Seq( pos ), flipped ) =>
        val root = ralproof.formulas
        val principial = ralproof.mainFormulas.head._2
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        val eqlformula = parent1.conclusion( p1occ )

        def fa( boolseq: Sequent[Boolean] ) = findAuxOptionInAntecedent( eqlformula, lkparent2.conclusion, Seq(), boolseq )
        def fs( boolseq: Sequent[Boolean] ) = findAuxOptionInSuccedent( eqlformula, lkparent1.conclusion, Seq(), boolseq )

        // check if the eqformula is already in the antecedent of parent 2. if yes, use the unary rule, if not simulate the binary rule
        ( fa( lkparent2.conclusion.map( _ => true ) ), fs( ca2 ) ) match {
          case ( Some( eqidx ), _ ) =>
            val modulant = findAuxInAntecedent( parent2.conclusion( p2occ ), lkparent2.conclusion, Seq( eqidx ), ca2 )
            val rule = Equality( lkparent2, eqidx, modulant, flipped, Seq( pos ) )
            val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( lkparent2, ca2 ), false )
            contractEndsequent( ( rule, nca ), es )
          case ( _, Some( eqidx ) ) =>
            val wlkparent2 = WeakeningLeft( lkparent2, lkparent1.conclusion( eqidx ) )
            val nca = Projections.calculate_child_cut_ecs( wlkparent2.occConnectors( 0 ), ( lkparent2, ca2 ), true )
            val modulant = findAuxInAntecedent( parent2.conclusion( p2occ ), wlkparent2.conclusion, Seq( eqidx ), nca )
            val weqidx = wlkparent2.mainIndices( 0 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of WeakeningLeft!" )
            }
            val rule = Equality( wlkparent2, weqidx, modulant, flipped, Seq( pos ) )
            val nc2 = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( wlkparent2, nca ), false )
            val ruleeqidx = rule.mainIndices( 1 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of Equation (left)!" )
            }
            val cutrule = Cut( lkparent1, eqidx, rule, ruleeqidx )
            val cnca = Projections.calculate_child_cut_ecs( cutrule.occConnectors( 0 ), cutrule.occConnectors( 1 ),
              ( lkparent1, ca1 ), ( wlkparent2, nca ), false )

            contractEndsequent( ( cutrule, cnca ), es )
          case ( None, None ) =>
            throw new Exception( s"Could not find equation $eqlformula!" )
        }

      case RalPara( parent1, p1occ, parent2, p2occ @ Suc( _ ), Seq( pos ), flipped ) =>
        val root = ralproof.formulas
        val principial = ralproof.mainFormulas.head._2
        val ( lkparent1, ca1 ) = ceres_omega( projections, parent1, es, struct )
        val ( lkparent2, ca2 ) = ceres_omega( projections, parent2, es, struct )

        val eqlformula = parent1.conclusion( p1occ )

        def fa( boolseq: Sequent[Boolean] ) = findAuxOptionInAntecedent( eqlformula, lkparent2.conclusion, Seq(), boolseq )
        def fs( boolseq: Sequent[Boolean] ) = findAuxOptionInSuccedent( eqlformula, lkparent1.conclusion, Seq(), boolseq )

        // check if the eqformula is already in the antecedent of parent 2. if yes, use the unary rule, if not simulate the binary rule
        ( fa( lkparent2.conclusion.map( _ => true ) ), fs( ca2 ) ) match {
          case ( Some( eqidx ), _ ) =>
            val modulant = findAuxInSuccedent( parent2.conclusion( p2occ ), lkparent2.conclusion, Seq( eqidx ), ca2 )
            val rule = Equality( lkparent2, eqidx, modulant, flipped, Seq( pos ) )
            val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( lkparent2, ca2 ), false )
            contractEndsequent( ( rule, nca ), es )
          case ( _, Some( eqidx ) ) =>
            val wlkparent2 = WeakeningRight( lkparent2, lkparent1.conclusion( eqidx ) )
            val nca = Projections.calculate_child_cut_ecs( wlkparent2.occConnectors( 0 ), ( lkparent2, ca2 ), true )
            val modulant = findAuxInSuccedent( parent2.conclusion( p2occ ), wlkparent2.conclusion, Seq( eqidx ), nca )
            val weqidx = wlkparent2.mainIndices( 0 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of WeakeningLeft!" )
            }
            val rule = Equality( wlkparent2, weqidx, modulant, flipped, Seq( pos ) )
            val nc2 = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), ( wlkparent2, nca ), false )
            val ruleeqidx = rule.mainIndices( 1 ) match {
              case a @ Ant( _ ) => a
              case _            => throw new Exception( "Error in constructor of Equation (left)!" )
            }
            val cutrule = Cut( lkparent1, eqidx, rule, ruleeqidx )
            val cnca = Projections.calculate_child_cut_ecs( cutrule.occConnectors( 0 ), cutrule.occConnectors( 1 ),
              ( lkparent1, ca1 ), ( wlkparent2, nca ), false )

            contractEndsequent( ( cutrule, cnca ), es )
          case ( None, None ) =>
            throw new Exception( s"Could not find equation $eqlformula!" )
        }

      case RalSub( parent, sub ) =>
        val root = ralproof.formulas
        val ( lkparent, ca ) = ceres_omega( projections, parent, es, struct )
        val ( rule, mapping ) = applySubstitution( lkparent, sub )
        //TODO: we assume here that the indices in the substituted proof and in the parents are the same
        ( rule, ca )

      case _ => throw new Exception( "Unhandled case: " + ralproof )
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
      throw new Exception( s"Could not find the auxiliary formula $aux in antecedent of $sequent with exclusion list $exclusion_list" )
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
      throw new Exception( s"Could not find the auxiliary formula $aux in succedent of $sequent with exclusion list $exclusion_list" )
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
      val a1 = findAuxInAntecedent( fo, proof.conclusion, Seq(), ca )
      val a2 = findAuxInAntecedent( fo, proof.conclusion, Seq( a1 ), ca )
      val rule = ContractionLeft( proof, a1, a2 )
      val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), rp, false )
      ( rule, nca )
    } )
    val contr_right = es.succedent.foldLeft( p )( ( rp, fo ) => {
      val ( proof, ca ) = rp
      val a1 = findAuxInSuccedent( fo, proof.conclusion, Seq(), ca )
      val a2 = findAuxInSuccedent( fo, proof.conclusion, Seq( a1 ), ca )
      val rule = ContractionRight( proof, a1, a2 )
      val nca = Projections.calculate_child_cut_ecs( rule.occConnectors( 0 ), rp, false )
      ( rule, nca )
    } )
    contr_right
  }

  /* removes the final end-sequent from a projection's current end-sequent */
  def filterEndsequent( root: LabelledSequent, cut_anc: Sequent[Boolean] ) =
    root.zipWithIndex.filter( x => cut_anc( x._2 ) ).map( _._1 )

  def diffModuloOccurrence( from: Seq[LabelledFormula], what: Seq[( RalProof.Label, HOLFormula )] ) = {
    what.foldLeft( from.toList )( ( l, occ ) =>
      removeFirstWhere( l, ( x: LabelledFormula ) => x._1 == occ._1 && x._2 == occ._2 ) )
  }

}
