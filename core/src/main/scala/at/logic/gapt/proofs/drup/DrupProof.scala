package at.logic.gapt.proofs.drup

import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.resolution._

import scala.collection.mutable

sealed abstract class DrupProofLine extends Product {
  def clause: HOLClause
  override def toString = s"[${productPrefix.stripPrefix( "Drup" ).toLowerCase}] $clause"
}

/** Input clause in a DRUP proof. */
case class DrupInput( clause: HOLClause ) extends DrupProofLine
/**
 * Derived clause in a DRUP proof.
 *
 * The clause is not only required to be a consequence of the previous
 * clauses in the proof, but also RUP (a strictly stronger requirement):
 *
 * Given a set of clauses Γ and a clause C, then C has the property RUP with regard to Γ iff
 * Γ, ¬C can be refuted with only unit propagation.
 */
case class DrupDerive( clause: HOLClause ) extends DrupProofLine
/**
 * Forgets a clause in a DRUP proof.
 *
 * This inference is not necessary for completeness, it is mainly a
 * performance optimization since it speeds up the unit propagation in [[DrupDerive]].
 */
case class DrupForget( clause: HOLClause ) extends DrupProofLine

/**
 * DRUP proof.
 *
 * A DRUP proof consists of a sequence of clauses.  Each clause is either a [[DrupInput]], a [[DrupDerive]], or a [[DrupForget]].
 */
case class DrupProof( refutation: Seq[DrupProofLine] ) {
  override def toString = refutation.reverse.mkString( "\n" )
}
object DrupProof {
  def apply( cnf: Iterable[HOLClause], refutation: Seq[DrupProofLine] ): DrupProof =
    DrupProof( cnf.map( DrupInput ).toSeq ++ refutation )
}

object DrupToResolutionProof {
  def unitPropagationProver( cnf0: Set[ResolutionProof] ): ResolutionProof = {
    val cnf = cnf0.to[mutable.Set]

    var didPropagate = true
    while ( didPropagate ) {
      for ( c <- cnf if c.conclusion.isEmpty ) return c
      didPropagate = false
      for {
        c1 <- cnf if c1.conclusion.size == 1
        ( a1, i1 ) <- c1.conclusion.zipWithIndex
        c2 <- cnf
        ( a2, i2 ) <- c2.conclusion.zipWithIndex
        if !i1.sameSideAs( i2 )
        if a1 == a2
      } {
        didPropagate = true
        cnf -= c2
        cnf += Factor(
          if ( i1.isSuc ) Resolution( c1, i1, c2, i2 )
          else Resolution( c2, i2, c1, i1 )
        )
      }
    }

    throw new IllegalArgumentException
  }

  def unitPropagationReplay( cnf: Iterable[ResolutionProof], toDerive: HOLClause ): ResolutionProof = {
    val negatedUnitClauses = toDerive.map( Sequent() :+ _, _ +: Sequent() ).elements.toSet[HOLSequent]
    val inputClausesForProver = cnf.map( p => p.conclusion -> p ).toMap
    val emptyClause = unitPropagationProver( ( inputClausesForProver.keySet ++ negatedUnitClauses ).map( Input ) )
    val derivation = tautologifyInitialUnitClauses( emptyClause, negatedUnitClauses )
    mapInputClauses( derivation )( inputClausesForProver )
  }

  def apply( drup: DrupProof ): ResolutionProof = {
    val cnf = mutable.Set[ResolutionProof]()
    drup.refutation foreach {
      case DrupInput( clause ) =>
        cnf += Input( clause )
      case DrupDerive( clause ) =>
        cnf += unitPropagationReplay( cnf, clause )
      case DrupForget( clause ) =>
        cnf.retain( !_.conclusion.multiSetEquals( clause ) )
    }
    simplifyResolutionProof( cnf.find( _.conclusion.isEmpty ).get )
  }
}