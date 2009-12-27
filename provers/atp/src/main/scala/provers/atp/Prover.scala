/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.propositions._
import at.logic.parsing.calculi.ResolutionParser

/**
 * A generic prover for resolution calculus
 */
trait Prover {
  /**
   * Refutes input clauses if possible
   * @param clausesInput the input clauses
   * @return a stream that instantiate all possible refutations
   */
  def refute(clausesInput: ResolutionParser) : Stream[Tuple2[ResolutionProof, Substitution]] = {
    val clauses  = clausesInput.getClauseList()
    Stream()
  }
}
