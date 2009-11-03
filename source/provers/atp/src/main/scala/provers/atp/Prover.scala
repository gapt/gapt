/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

//import at.logic.syntax.calculus.RuleA
//import at.logic.syntax.calculus.resolution._
//import at.logic.unification.Unifier
//import at.logic.parsing.calculus.SequentsParser

/**
 * A generic prover in resolution calculus
 */
class Prover
{
  /**
   * Refutes input clauses if possible
   * @param clausesInput the input clauses
   * @return an Option that is not None if a refutation exists. Then it contains aa tuple of a resolution proof and a unifier
   */
  /*def refute(clausesInput: SequentsParser[Clause]) : Option[(ResolutionProof[RuleA], Unifier)] = {
    val clauses  = clausesInput.getSequents()
    None  
  }*/
}
