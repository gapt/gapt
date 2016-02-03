package at.logic.gapt.proofs.resolution

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFn
import at.logic.gapt.proofs._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.{ ResolutionProver, groundFreeVariables }
import at.logic.gapt.utils.logging.Logger

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
      pairs:             List[( LambdaExpression, LambdaExpression )],
      alreadyFixedSubst: Map[Var, LambdaExpression]
    ): Traversable[Substitution] =
      pairs match {
        case ( ( Eq( t1, s1 ), Eq( t2, s2 ) ) :: rest ) =>
          apply( ( t1 -> t2 ) :: ( s1 -> s2 ) :: rest, alreadyFixedSubst ).toSeq ++
            apply( ( t1 -> s2 ) :: ( s1 -> t2 ) :: rest, alreadyFixedSubst ).toSeq
        case _ => super.apply( pairs, alreadyFixedSubst )
      }
  }

  def tryDeriveBySubsumptionModEq( to: HOLClause, from: HOLClause ): Option[ResolutionProof] =
    for ( s <- clauseSubsumption( from, to, multisetSubsumption = false, matchingAlgorithm = matchingModEq ) ) yield {
      var p = Factor( Instance( InputClause( from ), s ) )._1

      val needToFlip = for ( ( a, i ) <- p.conclusion.zipWithIndex ) yield a match {
        case _ if to.contains( a, i isSuc ) => false
        case Eq( t, s ) if to.contains( Eq( s, t ), i isSuc ) => true
        case _ => return None
      }

      for ( ( ( a, true ), i ) <- p.conclusion zip needToFlip zipWithIndex )
        p = Flip( p, p.conclusion.indexOfPol( a, i isSuc ) )

      p
    }

  def tryDeriveTrivial( to: HOLClause, from: Seq[HOLClause] ) = to match {
    case _ if from contains to => Some( InputClause( to ) )
    case HOLClause( Seq(), Seq( Eq( t, t_ ) ) ) if t == t_ => Some( ReflexivityClause( t ) )
    case HOLClause( Seq( a ), Seq( a_ ) ) if a == a_ => Some( TautologyClause( a ) )
    case _ => None
  }

  def tryDeriveViaResolution( to: HOLClause, from: Seq[HOLClause] ) =
    findDerivationViaResolution( to, from.toSet, Escargot )

  private def findFirstSome[A, B]( seq: Seq[A] )( f: A => Option[B] ): Option[B] =
    seq.view.flatMap( f( _ ) ).headOption

  def apply( p: ResolutionProof, cs: Seq[HOLClause] ): ResolutionProof =
    mapInputClauses( p ) { cls =>
      tryDeriveTrivial( cls, cs ).
        orElse( findFirstSome( cs )( tryDeriveBySubsumptionModEq( cls, _ ) ) ).
        orElse( tryDeriveViaResolution( cls, cs ) ).
        getOrElse {
          throw new IllegalArgumentException( s"Could not derive $cls from\n${cs mkString "\n"}" )
        }
    }

  def apply( p: ResolutionProof, endSequent: HOLSequent ): ResolutionProof =
    fixDerivation( p, CNFn toFClauseList endSequent.toFormula )
}

object tautologifyInitialUnitClauses {
  /**
   * Replace matching initial clauses by tautologies.
   *
   * If shouldTautologify is true for an initial unit clause +-a, then it is replaced by the tautology a:-a.  The
   * resulting resolution proof has the same structure as the original proof, and will hence contain many duplicate
   * literals originating from the new initial clauses as the new literals are not factored away.
   */
  def apply( p: ResolutionProof, shouldTautologify: HOLClause => Boolean ): ResolutionProof =
    p match {
      case InputClause( clause ) if shouldTautologify( clause ) && clause.size == 1 => TautologyClause( clause.elements.head )
      case InputClause( _ ) | ReflexivityClause( _ ) | TautologyClause( _ )         => p
      case Factor( p1, i1, i2 ) =>
        val newP1 = apply( p1, shouldTautologify )
        Factor( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).take( 2 ) )._1
      case Instance( p1, subst ) => Instance( apply( p1, shouldTautologify ), subst )
      case Resolution( p1, i1, p2, i2 ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        Resolution( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).head,
          newP2, newP2.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).filter( _ sameSideAs i2 ).head )
      case Paramodulation( p1, i1, p2, i2, pos, dir ) =>
        val newP1 = apply( p1, shouldTautologify )
        val newP2 = apply( p2, shouldTautologify )
        Paramodulation( newP1, newP1.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).filter( _ sameSideAs i1 ).head,
          newP2, newP2.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).filter( _ sameSideAs i2 ).head, pos, dir )
    }
}

object containedVariables {
  def apply( p: ResolutionProof ): Set[Var] =
    p.subProofs.flatMap { subProof => freeVariables( subProof.conclusion ) }
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
   * @return Resolution proof ending in a subclause of a, or None if prover9 couldn't prove the consequence.
   */
  def apply( a: HOLClause, bs: Set[_ <: HOLClause], prover: ResolutionProver = Escargot ): Option[ResolutionProof] = {
    val grounding = groundFreeVariables.getGroundingMap(
      freeVariables( a ),
      ( a.formulas ++ bs.flatMap( _.formulas ) ).flatMap( constants( _ ) ).toSet
    )

    val groundingSubst = Substitution( grounding )
    val negatedClausesA = a.
      map( groundingSubst( _ ) ).
      map( _.asInstanceOf[HOLAtom] ).
      map( Clause() :+ _, _ +: Clause() ).
      elements

    prover.getRobinsonProof( bs.toList ++ negatedClausesA.toList ) map { refutation =>
      val tautologified = tautologifyInitialUnitClauses( refutation, negatedClausesA.toSet )

      val toUnusedVars = rename( grounding.map( _._1 ).toSet, containedVariables( tautologified ) )
      val nonOverbindingUnground = grounding.map { case ( v, c ) => c -> toUnusedVars( v ) }
      val derivation = TermReplacement( tautologified, nonOverbindingUnground.toMap[LambdaExpression, LambdaExpression] )
      val derivationInOrigVars = Instance( derivation, Substitution( toUnusedVars.map( _.swap ) ) )

      simplifyResolutionProof( Factor( derivationInOrigVars )._1 )
    }
  }
}
