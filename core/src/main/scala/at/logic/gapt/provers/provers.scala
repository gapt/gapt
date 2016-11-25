package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.existentialClosure
import at.logic.gapt.proofs.epsilon.{ EpsilonProof, ExpansionProofToEpsilon }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofWithCut, ExpansionSequent, eliminateCutsET }
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.LKProof
import Session._
import Compilers._
import cats.{ Id, ~> }
import cats.implicits._

import scala.collection.mutable

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
  def isValid( formula: HOLFormula ): Boolean = isValid( HOLSequent( Nil, formula :: Nil ) )

  /**
   * @param seq The sequent whose validity should be checked.
   * @return True if the formula is valid.
   */
  def isValid( seq: HOLSequent ): Boolean = getLKProof( seq ) match {
    case Some( _ ) => true
    case None      => false
  }

  /**
   * Checks whether a formula is unsatisfiable.
   */
  def isUnsat( formula: HOLFormula ): Boolean = isValid( -formula )

  /**
   * Checks whether a set of clauses is unsatisfiable.
   */
  def isUnsat( cnf: Iterable[HOLClause] ): Boolean = isValid( existentialClosure( cnf ++: Sequent() map { _.toDisjunction } ) )

  /**
   * @param formula The formula that should be proved.
   * @return An LK-Proof of  :- formula, or None if not successful.
   */
  def getLKProof( formula: HOLFormula ): Option[LKProof] = getLKProof( HOLSequent( Nil, formula :: Nil ) )

  /**
   * @param seq The sequent that should be proved.
   * @return An LK-Proof of the sequent, or None if not successful.
   */
  def getLKProof( seq: HOLSequent ): Option[LKProof]

  def getExpansionProof( formula: HOLFormula ): Option[ExpansionProof] =
    getExpansionProof( Sequent() :+ formula )

  def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] =
    getLKProof( seq ) map { LKToExpansionProof( _ ) } map { eliminateCutsET( _ ) }

  def getEpsilonProof( seq: HOLSequent ): Option[EpsilonProof] =
    getExpansionProof( seq ) map { ExpansionProofToEpsilon( _ ) }
  def getEpsilonProof( formula: HOLFormula ): Option[EpsilonProof] =
    getEpsilonProof( Sequent() :+ formula )

  def runSession[A]( program: Session[A] ): A
}

trait OneShotProver extends Prover {
  override def runSession[A]( program: Session[A] ): A = program.foldMap[Id]( new StackSessionCompiler( this.isValid ) )
}

trait IncrementalProver extends Prover {
  def isValidProgram( seq: HOLSequent ): Session[Boolean] = {
    val ( groundSeq, _ ) = groundFreeVariables( seq )
    for {
      _ <- declareSymbolsIn( groundSeq.elements )
      _ <- assert( groundSeq.map( identity, -_ ).elements.toList )
      sat <- checkSat
    } yield !sat
  }
  override def getLKProof( seq: HOLSequent ): Option[LKProof] = ???
  override def isValid( seq: HOLSequent ): Boolean = runSession( isValidProgram( seq ) )
}