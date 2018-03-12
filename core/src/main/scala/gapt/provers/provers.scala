package gapt.provers

import gapt.expr._
import gapt.expr.hol.existentialClosure
import gapt.proofs.epsilon.{ EpsilonProof, ExpansionProofToEpsilon }
import gapt.proofs.expansion.{ ExpansionProof, eliminateCutsET }
import gapt.proofs.{ Context, HOLClause, HOLSequent, MutableContext, Sequent }
import gapt.proofs.lk.LKToExpansionProof
import gapt.proofs.lk.LKProof
import Session._
import Runners._
import gapt.utils.Maybe

/**
 * A prover that is able to refute HOL sequents/formulas (or subsets
 * of HOL, like propositional logic).
 *
 * TODO: exceptions to indicate that a formula is not supported (e.g.
 * for propositional provers).
 *
 * Implementors may want to override isValid(seq) to avoid parsing
 * proofs.
 */

trait Prover {
  /**
   * @param formula The formula whose validity should be checked.
   * @return True if the formula is valid.
   */
  def isValid( formula: Formula )( implicit ctx: Maybe[Context] ): Boolean = isValid( HOLSequent( Nil, formula :: Nil ) )

  /**
   * @param seq The sequent whose validity should be checked.
   * @return True if the formula is valid.
   */
  def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = getLKProof( seq ) match {
    case Some( _ ) => true
    case None      => false
  }

  /**
   * Checks whether a formula is unsatisfiable.
   */
  def isUnsat( formula: Formula )( implicit ctx: Maybe[Context] ): Boolean = isValid( -formula )

  /**
   * Checks whether a set of clauses is unsatisfiable.
   */
  def isUnsat( cnf: Iterable[HOLClause] )( implicit ctx: Maybe[Context] ): Boolean = isValid( existentialClosure( cnf ++: Sequent() map { _.toDisjunction } ) )

  /**
   * @param formula The formula that should be proved.
   * @return An LK-Proof of  :- formula, or None if not successful.
   */
  def getLKProof( formula: Formula )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    getLKProof( HOLSequent( Nil, formula :: Nil ) )

  /**
   * @param seq The sequent that should be proved.
   * @return An LK-Proof of the sequent, or None if not successful.
   */
  def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof]

  def getExpansionProof( formula: Formula )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] =
    getExpansionProof( Sequent() :+ formula )

  def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] =
    getLKProof( seq ) map { LKToExpansionProof( _ ) } map { eliminateCutsET( _ ) }

  def getEpsilonProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[EpsilonProof] =
    getExpansionProof( seq ) map { ExpansionProofToEpsilon( _ ) }
  def getEpsilonProof( formula: Formula )( implicit ctx: Maybe[MutableContext] ): Option[EpsilonProof] =
    getEpsilonProof( Sequent() :+ formula )

  /**
   * Method for running a session.
   * @param program A proof session.
   * @tparam A The return type of the session.
   * @return The result of running the session.
   */
  def runSession[A]( program: Session[A] ): A
}

/**
 * A prover that interprets Sessions as stack operations.
 */
trait OneShotProver extends Prover {
  override def runSession[A]( program: Session[A] ): A = new StackSessionRunner( this.isValid ).run( program )
}

/**
 * A prover that determines validity via an incremental proof session.
 */
trait IncrementalProver extends Prover {

  def treatUnknownAsSat = false

  /**
   * Tests the validity of a sequent.
   */
  def isValidProgram( seq: HOLSequent ): Session[Boolean] = {
    val ( groundSeq, _ ) = groundFreeVariables( seq )
    for {
      _ <- declareSymbolsIn( groundSeq.elements )
      _ <- assert( groundSeq.map( identity, -_ ).elements.toList )
      unsat <- checkUnsat
    } yield unsat.getOrElse {
      if ( treatUnknownAsSat ) false
      else throw new IllegalArgumentException
    }
  }

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = ???
  override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = runSession( isValidProgram( seq ) )
}