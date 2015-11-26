package at.logic.gapt.provers

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lkNew.LKToExpansionProof
import at.logic.gapt.proofs.lkNew.LKProof

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
   * @param formula The formula that should be proved.
   * @return An LK-Proof of  :- formula, or None if not successful.
   */
  def getLKProof( formula: HOLFormula ): Option[LKProof] = getLKProof( HOLSequent( Nil, formula :: Nil ) )

  /**
   * @param seq The sequent that should be proved.
   * @return An LK-Proof of the sequent, or None if not successful.
   */
  def getLKProof( seq: HOLSequent ): Option[LKProof]

  def getExpansionSequent( seq: HOLSequent ): Option[ExpansionSequent] =
    getLKProof( seq ).map( LKToExpansionProof( _ ) )

  /**
   * Starts an incremental proving session.
   */
  def startIncrementalSession(): IncrementalProvingSession
}

trait OneShotProver extends Prover { self: Prover =>
  class FakeIncrementalSession extends IncrementalProvingSession {
    val formulaStack = mutable.Stack[Set[HOLFormula]]()
    var assertedFormulas = Set[HOLFormula]()

    def push() = formulaStack push assertedFormulas
    def pop() = { assertedFormulas = formulaStack.pop }

    def declareSymbolsIn( expressions: TraversableOnce[LambdaExpression] ) = ()
    def assert( formula: HOLFormula ) = assertedFormulas += formula
    def checkSat() = !self.isValid( assertedFormulas ++: Sequent() )

    def close() = ()
  }

  def startIncrementalSession() = new FakeIncrementalSession
}

trait IncrementalProver extends Prover {
  override def getLKProof( seq: HOLSequent ): Option[LKProof] = ???
  override def isValid( seq: HOLSequent ) = for ( session <- startIncrementalSession() ) yield {
    val ( groundSeq, _ ) = groundFreeVariables( seq )
    session declareSymbolsIn groundSeq.elements
    groundSeq.map( identity, -_ ) foreach session.assert
    !session.checkSat()
  }
}

/**
 * Interactive interface to an interactive prover like an SMT solver.
 *
 * The methods on this trait are chosen for similarity to the SMT-LIB
 * standard.  You can imagine that an instance of this trait is a single
 * SMT solver processing commands interactively.
 */
trait IncrementalProvingSession {
  /**
   * Starts a new scope.  All commands that are issued will be reverted after the corresponding call to pop().
   */
  def push()

  /**
   * Undos the commands since the corresponding push().
   */
  def pop()

  /**
   * Declares function symbols and base types from expressions.
   */
  def declareSymbolsIn( expressions: LambdaExpression* ): Unit = declareSymbolsIn( expressions )
  /**
   * Declares function symbols and base types from expressions.
   */
  def declareSymbolsIn( expressions: TraversableOnce[LambdaExpression] ): Unit

  /**
   * Adds an assertion.
   */
  def assert( formula: HOLFormula )

  /**
   * Checks whether the currently asserted formulas are satisfiable.
   */
  def checkSat(): Boolean

  /** Closes the process. */
  def close()

  /** Run f in its own scope, i.e. push(); f; pop() */
  def withScope[A]( f: => A ): A = { push(); try f finally pop() }

  def foreach( f: this.type => Unit ): Unit = flatMap( f )
  def map[A]( f: this.type => A ): A = flatMap( f )
  def flatMap[A]( f: this.type => A ): A = try f( this ) finally close()
}