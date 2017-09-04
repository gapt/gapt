package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFn
import at.logic.gapt.proofs._
import at.logic.gapt.provers.escargot.{ Escargot, NonSplittingEscargot }
import at.logic.gapt.provers.{ ResolutionProver, groundFreeVariables }
import at.logic.gapt.utils.Logger

import scala.collection.immutable.HashMap

/**
 *  Sometimes, we have a resolution refutation R of a set of clauses C
 *  and want a refutation R' of a set C' such that C implies C'.
 *
 *  This algorithm tries to obtain R' by trying to replace clauses c
 *  from C in R by derivations of C from C'.
 *
 *  In general, if R is a derivation of a clause c, the result R' of fixDerivation(R)
 *  is a derivation of a subclause of c.
 */

object fixDerivation extends Logger {
  object matchingModEq extends syntacticMatching {
    override def apply(
      pairs:             List[( Expr, Expr )],
      alreadyFixedSubst: PreSubstitution ): Traversable[Substitution] =
      pairs match {
        case ( ( Eq( t1, s1 ), Eq( t2, s2 ) ) :: rest ) =>
          apply( ( t1 -> t2 ) :: ( s1 -> s2 ) :: rest, alreadyFixedSubst ).toSeq ++
            apply( ( t1 -> s2 ) :: ( s1 -> t2 ) :: rest, alreadyFixedSubst ).toSeq
        case _ => super.apply( pairs, alreadyFixedSubst )
      }
  }

  def tryDeriveBySubsumptionModEq( to: HOLClause, from: HOLClause ): Option[ResolutionProof] =
    for ( s <- clauseSubsumption( from, to, matchingAlgorithm = matchingModEq ) ) yield {
      var p = Factor( Subst( Input( from ), s ) )

      val needToFlip = for ( ( a, i ) <- p.conclusion.zipWithIndex ) yield a match {
        case _ if to.contains( a, i.polarity ) => false
        case Eq( t, s ) if to.contains( Eq( s, t ), i.polarity ) => true
        case _ => return None
      }

      for ( ( ( a, true ), i ) <- p.conclusion zip needToFlip zipWithIndex )
        p = Flip( p, p.conclusion.indexOfPol( a, i.polarity ) )

      p = Factor( p )
      p
    }

  def tryDeriveTrivial( to: HOLClause, from: Seq[HOLClause] ) = to match {
    case _ if from contains to => Some( Input( to ) )
    case HOLClause( Seq(), Seq( Eq( t, t_ ) ) ) if t == t_ => Some( Refl( t ) )
    case HOLClause( Seq( a ), Seq( a_ ) ) if a == a_ => Some( Taut( a ) )
    case _ => None
  }

  def tryDeriveViaResolution( to: HOLClause, from: Seq[HOLClause] ) =
    findDerivationViaResolution( to, from.toSet, Escargot )

  private def findFirstSome[A, B]( seq: Seq[A] )( f: A => Option[B] ): Option[B] =
    seq.view.flatMap( f( _ ) ).headOption

  def apply( p: ResolutionProof, cs: Iterable[ResolutionProof] ): ResolutionProof = {
    val csMap = cs.view.map( c => c.conclusion -> c ).toMap
    mapInputClauses( apply( p, csMap.keySet.map( _.map( _.asInstanceOf[Atom] ) ) ) )( csMap )
  }
  def apply( p: ResolutionProof, cs: Traversable[HOLClause] ): ResolutionProof =
    apply( p, cs.toSeq )
  def apply( p: ResolutionProof, cs: Seq[HOLClause] ): ResolutionProof =
    mapInputClauses( p ) { seq =>
      val cls = seq.map( _.asInstanceOf[Atom] )
      tryDeriveTrivial( cls, cs ).
        orElse( findFirstSome( cs )( tryDeriveBySubsumptionModEq( cls, _ ) ) ).
        orElse( tryDeriveViaResolution( cls, cs ) ).
        getOrElse {
          throw new IllegalArgumentException( s"Could not derive $cls from\n${cs mkString "\n"}" )
        }
    }

  def apply( p: ResolutionProof, endSequent: HOLSequent ): ResolutionProof = {
    val cnf = structuralCNF( endSequent, structural = false )
    mapInputClauses( fixDerivation( p, cnf.map( _.conclusion.map( _.asInstanceOf[Atom] ) ) ) )( cls => cnf.find( _.conclusion == cls ).get )
  }
}

object tautologifyInitialUnitClauses {
  /**
   * Replace matching initial clauses by tautologies.
   *
   * If shouldTautologify is true for an initial unit clause +-a, then it is replaced by the tautology a:-a.  The
   * resulting resolution proof has the same structure as the original proof.
   */
  def apply( p: ResolutionProof, shouldTautologify: HOLSequent => Boolean ): ResolutionProof =
    mapInputClauses( p ) {
      case clause @ Sequent( Seq(), Seq( a ) ) if shouldTautologify( clause ) =>
        Taut( a )
      case clause @ Sequent( Seq( a ), Seq() ) if shouldTautologify( clause ) =>
        Taut( a )
      case clause => Input( clause )
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
   * @param prover Prover to obtain a resolution refutation of the consequence bs |= a from.
   * @return Resolution proof ending in a subclause of a, or None if the prover couldn't prove the consequence.
   */
  def apply( a: HOLClause, bs: Set[_ <: HOLClause], prover: ResolutionProver = NonSplittingEscargot ): Option[ResolutionProof] = {
    val grounding = groundFreeVariables.getGroundingMap(
      freeVariables( a ),
      ( a.formulas ++ bs.flatMap( _.formulas ) ).flatMap( constants( _ ) ).toSet )

    val groundingSubst = Substitution( grounding )
    val negatedClausesA = a.
      map( groundingSubst( _ ) ).
      map( _.asInstanceOf[Atom] ).
      map( Clause() :+ _, _ +: Clause() ).
      elements

    prover.getResolutionProof( bs ++ negatedClausesA ) map { refutation =>
      val tautologified = tautologifyInitialUnitClauses( eliminateSplitting( refutation ), negatedClausesA.toSet )

      val toUnusedVars = rename( grounding.map( _._1 ), containedNames( tautologified ) )
      val nonOverbindingUnground = grounding.map { case ( v, c ) => c -> toUnusedVars( v ) }
      val derivation = TermReplacement( tautologified, nonOverbindingUnground.toMap[Expr, Expr] )
      val derivationInOrigVars = Subst( derivation, Substitution( toUnusedVars.map( _.swap ) ) )

      simplifyResolutionProof( derivationInOrigVars )
    }
  }
}
