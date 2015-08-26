package at.logic.gapt.proofs.resolution

import at.logic.gapt.algorithms.rewriting.{ NameReplacement, RenameResproof }
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.subsumption.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.provers.atp.SearchDerivation
import at.logic.gapt.provers.groundFreeVariables
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.utils.logging.Logger

import scala.collection.immutable.HashMap
import scala.collection.mutable

/**
 *  Sometimes, we have a resolution refutation R of a set of clauses C
 *  and want a refutation R' of a set C' such that C implies C'.
 *
 *  This algorithm tries to obtain R' by trying to replace clauses c
 *  from C in R by derivations of C from C' in the following way:
 *
 *  - If c is in C' or c is an instance of reflexivity, do nothing.
 *  - If c is subsumed by some c' in C', derive c from c' by factoring.
 *  - Otherwise, try to derive c from C' by paramodulation and symmetry (prover9 often needs
 *    this, and the check is usually fast),
 *  - Otherwise, try to derive c from C' by propositional resolution.
 *
 *  If none of this works, we issue a warning and keep the clause c. If no warning is issued
 *  and the algorithm terminates, the result is the desired R'.
 *
 *  In general, if R is a derivation of a clause c, the result R' of fixDerivation(R)
 *  is a derivation of a subclause of c.
 */

object fixDerivation extends Logger {
  private def getSymmetryMap( to: Pair[Seq[FOLFormula], Seq[FOLFormula]], from: Pair[Seq[FOLFormula], Seq[FOLFormula]] ) = {
    var err = false
    def createMap( from: Seq[FOLFormula], to: Seq[FOLFormula] ) = {
      ( from zip from.indices ).foldLeft( HashMap[Int, Int]() ) {
        case ( map, ( from_f, from_i ) ) => {
          val to_i = to.indexWhere( to_f => ( from_f == to_f ) || ( ( from_f, to_f ) match {
            case ( Eq( from_l, from_r ), Eq( to_l, to_r ) ) if from_l == to_r && from_r == to_l => true
            case _ => false
          } ) )
          if ( to_i != -1 )
            map + ( ( from_i, to_i ) )
          else {
            err = true
            map
          }
        }
      }
    }
    val neg_map = createMap( from._1, to._1 )
    val pos_map = createMap( from._2, to._2 )
    if ( err )
      None
    else
      Some( ( neg_map, pos_map ) )
  }
  private def convertSequent( seq: HOLSequent ) =
    ( seq.antecedent.map( f => f.asInstanceOf[FOLFormula] ), seq.succedent.map( f => f.asInstanceOf[FOLFormula] ) )
  private def applySymm( p: RobinsonResolutionProof, f: FOLFormula, pos: Boolean ) =
    {
      val ( left, right ) = f match {
        case Eq( l, r ) => ( l, r )
      }
      val newe = Eq( right, left )
      val refl = Eq( left, left )
      val s = FOLSubstitution()
      if ( pos ) {
        val irefl = InitialClause( Nil, refl :: Nil )
        Paramodulation( p, irefl, f, refl, newe, s, pos )
      } else {
        val init = InitialClause( newe :: Nil, newe :: Nil )
        val init2 = InitialClause( newe :: Nil, newe :: Nil )
        val eq1 = Paramodulation( init, p, newe, f, refl, s, pos )
        val eq2 = Paramodulation( init2, eq1, newe, refl, newe, s, pos )
        Factor( eq2, newe, 3, pos, s )
      }
    }
  def tryDeriveBySymmetry( to: HOLClause, from: HOLSequent ): Option[RobinsonResolutionProof] =
    getSymmetryMap( convertSequent( to ), convertSequent( from ) ) map {
      case ( neg_map, pos_map ) =>
        trace( "deriving " + to + " from " + from + " by symmetry" )
        val my_to = convertSequent( to )
        val my_from = convertSequent( from )
        val ( neg_map, pos_map ) = getSymmetryMap( my_to, my_from ).get
        val init = InitialClause( from.antecedent.map( _.asInstanceOf[FOLFormula] ), from.succedent.map( _.asInstanceOf[FOLFormula] ) )

        var my_from_s = ( List[FOLFormula](), List[FOLFormula]() )
        var neg_map_s = HashMap[Int, Int]()
        var pos_map_s = HashMap[Int, Int]()

        // add symmetry derivations
        val s_neg = neg_map.keySet.foldLeft( init )( ( p, i ) => {
          val f = my_from._1( i )
          val to_i = neg_map( i )
          neg_map_s = neg_map_s + ( my_from_s._1.size -> to_i )
          f match {
            case Eq( _, _ ) if my_to._1( to_i ) != f => {
              my_from_s = ( my_from_s._1 :+ my_to._1( to_i ), my_from_s._2 )
              applySymm( p, f, false )
            }
            case _ => {
              my_from_s = ( my_from_s._1 :+ f, my_from_s._2 )
              p
            }
          }
        } )
        val s_pos = pos_map.keySet.foldLeft( s_neg )( ( p, i ) => {
          val f = my_from._2( i )
          val to_i = pos_map( i )
          pos_map_s = pos_map_s + ( my_from_s._2.size -> to_i )
          f match {
            case Eq( _, _ ) if my_to._2( to_i ) != f => {
              my_from_s = ( my_from_s._1, my_from_s._2 :+ my_to._2( to_i ) )
              applySymm( p, f, true )
            }
            case _ => {
              my_from_s = ( my_from_s._1, my_from_s._2 :+ f )
              p
            }
          }
        } )

        assert( to.isSubMultisetOf( s_pos.root.toHOLSequent ) )

        // contract some formulas if the maps are not injective
        val c_neg = neg_map_s.values.toSeq.distinct.foldLeft( s_pos )( ( p, i ) => {
          val indices = neg_map_s.filterKeys( k => neg_map_s( k ) == i ).keySet
          val form = my_from_s._1( indices.head )

          if ( indices.size > 1 )
            Factor( p, form, indices.size, false, FOLSubstitution() )
          else
            p
        } )

        pos_map_s.values.toSeq.distinct.foldLeft( c_neg )( ( p, i ) => {
          val indices = pos_map_s.filterKeys( k => pos_map_s( k ) == i ).keySet
          val form = my_from_s._2( indices.head )
          if ( indices.size > 1 )
            Factor( p, form, indices.size, true, FOLSubstitution() )
          else
            p
        } )
    }

  private val subsumption_alg = StillmanSubsumptionAlgorithmFOL
  def tryDeriveByFactor( to: HOLClause, from_c: HOLSequent ): Option[RobinsonResolutionProof] =
    subsumption_alg.subsumes_by( from_c, to ) map { s =>
      val from = InitialClause( from_c.antecedent.map( _.asInstanceOf[FOLFormula] ), from_c.succedent.map( _.asInstanceOf[FOLFormula] ) )
      val from_s = HOLClause( from_c.antecedent.map( s( _ ).asInstanceOf[HOLAtom] ), from_c.succedent.map( s( _ ).asInstanceOf[HOLAtom] ) )
      // make a first Factor inference that does not contract, but applies
      // the FOLSubstitution
      val first = if ( !from_c.antecedent.isEmpty )
        Factor( from, from_c.antecedent.head, 1, false, s )
      else
        Factor( from, from_c.succedent.head, 1, true, s )
      val proof = from_s.negative.toSet.foldLeft( first )( ( proof, atom ) => {
        val cnt = from_s.negative.count( _ == atom ) - to.negative.count( _ == atom ) + 1
        Factor( proof, atom, cnt, false, FOLSubstitution() )
      } )
      from_s.positive.toSet.foldLeft( proof )( ( proof, atom ) => {
        val cnt = from_s.positive.count( _ == atom ) - to.positive.count( _ == atom ) + 1
        Factor( proof, atom, cnt, true, FOLSubstitution() )
      } )
    }

  private def isReflexivity( c: HOLClause ) =
    c.positive.exists( a => a match {
      case Eq( x, y ) if x == y => true
      case _                    => false
    } )
  private def isTautology( c: HOLClause ) = c.positive.exists( a => c.negative.exists( b => a == b ) )
  def tryDeriveTrivial( to: HOLClause, from: Seq[HOLSequent] ) = {
    val cls_sequent = HOLSequent( to.negative.map( _.asInstanceOf[FOLFormula] ), to.positive.map( _.asInstanceOf[FOLFormula] ) )
    if ( from.contains( cls_sequent ) || isReflexivity( to ) || isTautology( to ) ) Some( InitialClause( to ) )
    else None
  }

  def tryDeriveViaSearchDerivation( to: HOLClause, from: Seq[HOLSequent] ) = {
    val cls_sequent = HOLSequent( to.negative.map( _.asInstanceOf[FOLFormula] ), to.positive.map( _.asInstanceOf[FOLFormula] ) )
    SearchDerivation( from, cls_sequent, true ) flatMap { d =>
      val ret = d.asInstanceOf[RobinsonResolutionProof]
      if ( ret.root.toHOLSequent != to ) {
        val ret_seq = HOLSequent( ret.root.antecedent.map( _.formula ), ret.root.succedent.map( _.formula ) )
        // FIXME: replace InitialClause(ret_seq) by ret in the following proof
        // tryDeriveByFactor( to, ret_seq )
        None
      } else {
        Some( ret )
      }
    }
  }

  private val prover9 = new Prover9Prover
  def tryDeriveViaResolution( to: HOLClause, from: Seq[HOLSequent] ) =
    if ( prover9 isInstalled )
      findDerivationViaResolution( to, from.map { seq => HOLClause( seq.antecedent, seq.succedent ) }.toSet )
    else
      None

  private def findFirstSome[A, B]( seq: Seq[A] )( f: A => Option[B] ): Option[B] =
    seq.view.flatMap( f( _ ) ).headOption

  def apply( p: RobinsonResolutionProof, cs: Seq[HOLSequent] ): RobinsonResolutionProof =
    mapInitialClauses( p ) { cls =>
      tryDeriveTrivial( cls, cs ).
        orElse( findFirstSome( cs )( tryDeriveByFactor( cls, _ ) ) ).
        orElse( findFirstSome( cs )( tryDeriveBySymmetry( cls, _ ) ) ).
        orElse( tryDeriveViaSearchDerivation( cls, cs ) ).
        orElse( tryDeriveViaResolution( cls, cs ) ).
        getOrElse {
          warn( "Could not derive " + cls + " from " + cs + " by symmetry or propositional resolution" )
          InitialClause( cls )
        }
    }
}

/**
 * Applies a function to each initial clause in a resolution proof, replacing the initial clause with a new proof.
 * The resulting proof may prove a smaller clause than the original one.
 */
object mapInitialClauses {
  def apply( p: RobinsonResolutionProof )( f: HOLClause => RobinsonResolutionProof ): RobinsonResolutionProof =
    apply( p, f, mutable.Map[RobinsonResolutionProof, RobinsonResolutionProof]() )

  private def apply(
    p:     RobinsonResolutionProof,
    f:     HOLClause => RobinsonResolutionProof,
    cache: mutable.Map[RobinsonResolutionProof, RobinsonResolutionProof]
  ): RobinsonResolutionProof = cache.getOrElseUpdate( p, p match {
    case InitialClause( cls ) => f( cls.toHOLClause )

    case Factor( r, par, List( lit1 ), s ) =>
      val rp = apply( par, f, cache )
      val form = lit1.head.formula
      val pos = par.root.succedent.contains( lit1.head )
      val cnt_ = if ( pos ) rp.root.succedent.count( _.formula == form ) - p.root.succedent.count( _.formula == form ) + 1
      else rp.root.antecedent.count( _.formula == form ) - p.root.antecedent.count( _.formula == form ) + 1
      val cnt = if ( cnt_ > 0 ) cnt_ else 0
      if ( cnt == 0 )
        rp
      else
        Factor( rp, form, cnt, pos, s )

    case Factor( r, par, List( lit1, lit2 ), s ) =>
      val rp = apply( par, f, cache )
      val form_left = lit1.head.formula
      val form_right = lit2.head.formula
      val cnt_left_ = rp.root.antecedent.count( _.formula == form_left ) - p.root.antecedent.count( _.formula == form_left )
      val cnt_right_ = rp.root.succedent.count( _.formula == form_right ) - p.root.succedent.count( _.formula == form_right )
      val cnt_left = if ( cnt_left_ > 0 ) cnt_left_ else 0
      val cnt_right = if ( cnt_right_ > 0 ) cnt_right_ else 0
      if ( cnt_left == 0 && cnt_right == 0 )
        rp
      else
        Factor( rp, form_left, cnt_left, form_right, cnt_right, s )

    case Variant( r, p, s ) => Variant( apply( p, f, cache ), s )

    case Resolution( r, p1, p2, a1, a2, s ) =>
      val rp1 = apply( p1, f, cache )
      val rp2 = apply( p2, f, cache )
      if ( !rp1.root.succedent.exists( _.formula == a1.formula ) )
        rp1
      else if ( !rp2.root.antecedent.exists( _.formula == a2.formula ) )
        rp2
      else
        Resolution( rp1, rp2, a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], s )

    case Paramodulation( r, p1, p2, a1, a2, p, s ) =>
      val rp1 = apply( p1, f, cache )
      val rp2 = apply( p2, f, cache )
      val right = p2.root.succedent.contains( a2 )
      if ( !rp1.root.succedent.exists( _.formula == a1.formula ) )
        rp1
      else if ( right && !rp2.root.succedent.exists( _.formula == a2.formula ) )
        rp2
      else if ( !right && !rp2.root.antecedent.exists( _.formula == a2.formula ) )
        rp2
      else
        Paramodulation( rp1, rp2, a1.formula.asInstanceOf[FOLFormula], a2.formula.asInstanceOf[FOLFormula], p.formula.asInstanceOf[FOLFormula], s, right )

    // this case is applicable only if the proof is an instance of RobinsonProofWithInstance
    case Instance( _, p, s ) => Instance( apply( p, f, cache ), s )
  } )
}

object tautologifyInitialClauses {
  private def findMatchingOccurrences( occ: FormulaOccurrence, from: OccClause, to: OccClause ): Seq[FormulaOccurrence] =
    if ( from.negative.contains( occ ) )
      to.negative.filter( _.formula == occ.formula )
    else
      to.positive.filter( _.formula == occ.formula )

  /**
   * Replace matching initial clauses by tautologies.
   *
   * If shouldTautologify is true for an initial clause Γ:-Δ, then it is replaced by the tautology Γ,Δ:-Γ,Δ.  The
   * resulting resolution proof has the same structure as the original proof, and will hence contain many duplicate
   * literals originating from the new initial clauses as the new literals are not factored away.
   */
  def apply( p: RobinsonResolutionProof, shouldTautologify: HOLClause => Boolean ): RobinsonResolutionProof =
    p match {
      case InitialClause( clause ) if shouldTautologify( clause.toHOLClause ) =>
        val allLiterals = ( clause.antecedent ++ clause.succedent ).map( _.formula ).map( _.asInstanceOf[FOLFormula] )
        InitialClause( allLiterals, allLiterals )
      case InitialClause( clause ) => p
      case Factor( clause, p1, List( occurrences ), subst ) =>
        Factor(
          apply( p1, shouldTautologify ),
          occurrences.head.formula, occurrences.size, p1.root.positive.contains( occurrences.head ), subst
        )
      case Variant( clause, p1, subst )  => Variant( apply( p1, shouldTautologify ), subst )
      case Instance( clause, p1, subst ) => Instance( apply( p1, shouldTautologify ), subst )
      case Resolution( clause, p1, p2, occ1, occ2, subst ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        val newOcc1 = newP1.root.succedent.find( _.formula == occ1.formula ).get
        val newOcc2 = newP2.root.antecedent.find( _.formula == occ2.formula ).get
        Resolution( newP1, newP2, newOcc1, newOcc2, subst )
      case Paramodulation( clause, p1, p2, occ1, occ2, main, subst ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        val newOcc1 = newP1.root.succedent.find( _.formula == occ1.formula ).get
        val newOcc2 = findMatchingOccurrences( occ2, p2.root, newP2.root ).head
        Paramodulation( newP1, newP2, newOcc1, newOcc2, main.formula.asInstanceOf[FOLFormula], subst )
    }
}

object containedVariables {
  def apply( p: RobinsonResolutionProof ): Set[FOLVar] =
    p.nodes.flatMap {
      case node: RobinsonResolutionProof =>
        freeVariables( node.root.toHOLSequent ).map( _.asInstanceOf[FOLVar] )
    }
}

object factorDuplicateLiterals {
  def apply( p: RobinsonResolutionProof ): RobinsonResolutionProof =
    p.root.literals.groupBy( l => ( l._1.formula, l._2 ) ).foldLeft( p ) {
      case ( p_, ( ( lit, pos ), occs ) ) =>
        Factor( p_, lit, occs.size, pos, FOLSubstitution() )
    }
}

object findDerivationViaResolution {
  /**
   * Finds a resolution derivation of a clause from a set of clauses.
   *
   * The resulting resolution proof ends in a subclause of the specified clause a, and its initial clauses are either
   * from bs, tautologies, or reflexivity.
   *
   * @param a Consequence to prove.
   * @param bs Set of initial clauses for the resulting proof.
   * @return Resolution proof ending in a subclause of a, or None if prover9 couldn't prove the consequence.
   */
  def apply( a: HOLClause, bs: Set[HOLClause] ): Option[RobinsonResolutionProof] = {
    val grounding = groundFreeVariables.getGroundingMap(
      freeVariables( a ),
      ( a.formulas ++ bs.flatMap( _.formulas ) ).flatMap( constants( _ ) ).toSet
    )

    val groundingSubst = FOLSubstitution( grounding )
    val negatedClausesA = a.negative.map { f => HOLClause( Seq(), Seq( groundingSubst( f ) ) ) } ++
      a.positive.map { f => HOLClause( Seq( groundingSubst( f ) ), Seq() ) }

    new Prover9Prover().getRobinsonProof( bs.toList ++ negatedClausesA.toList ) map { refutation =>
      val tautologified = tautologifyInitialClauses( refutation, negatedClausesA.toSet )

      val toUnusedVars = rename( grounding.map( _._1 ).toSet, containedVariables( tautologified ) )
      val nonOverbindingUnground = grounding.map { case ( v, c ) => c -> toUnusedVars( v ) }.toMap[FOLTerm, FOLTerm]
      val derivation = RenameResproof.rename_resproof( tautologified, Set(), nonOverbindingUnground )
      val derivationInOrigVars = Variant( derivation, FOLSubstitution( toUnusedVars.map( _.swap ) ) )

      factorDuplicateLiterals( derivationInOrigVars )
    }
  }
}
