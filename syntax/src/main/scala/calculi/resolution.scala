/* Description: Generic resolution calculus for any order. The solution to prevent functions with operator as symbols is to branch the term data structure into NamedTerm and GenTerm and here use only NamedTerm while in fol we use GenFunction[OType]. The solution is not very intuitive and there must be a better one. 
 */

package at.logic.syntax.calculus.resolution
import at.logic.syntax.language.{TermA,TypeA}
import at.logic.syntax.calculus

case class ClauseTermOccurrence(f: TermA[TypeA]) extends TermOccurrence(f)
case class Clause(ant : List[ClauseTermOccurrence], suc : List[ClauseTermOccurrence]) extends SequentA(ant,suc)

case object Initial extends NullaryRuleTypeA
case object Resolution extends BinaryRuleTypeA

trait ResolutionProof[+T <: RuleA] extends RuleA{
  this: T with ResolutionProof[T] =>
}
final case class InitialRule(s : Clause) extends NullaryRuleA(Initial,s) with ResolutionProof[InitialRule]
final case class ResolutionRule(u1 : ResolutionProof[RuleA], u2 : ResolutionProof[RuleA], c2 : Clause, a2 : ClauseTermOccurrence, p2 : ClauseTermOccurrence) extends BinaryRuleA(Resolution, u1, u2, c2, Some(List[ClauseTermOccurrence](a2)), Some(List[ClauseTermOccurrence](p2))) with ResolutionProof[ResolutionRule]
