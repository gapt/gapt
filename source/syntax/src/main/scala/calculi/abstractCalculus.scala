/* Description: Defines the basics of all calculi
 */

package at.logic.syntax.calculus
import at.logic.syntax.language.{TermA,TypeA}

abstract class RuleTypeA
abstract class NullaryRuleTypeA extends RuleTypeA
abstract class UnaryRuleTypeA extends RuleTypeA
abstract class BinaryRuleTypeA extends RuleTypeA

abstract class TermOccurrence(form : TermA[TypeA])
abstract class SequentA(antecedent : List[TermOccurrence], succedent : List[TermOccurrence])

abstract class RuleA(typ : RuleTypeA, conseq : SequentA, aux : Option[List[TermOccurrence]], prin : Option[List[TermOccurrence]])
abstract case class NullaryRuleA(tpe: NullaryRuleTypeA, c : SequentA) extends RuleA(tpe, c, None,None)
abstract case class UnaryRuleA(tpe: UnaryRuleTypeA, upper : RuleA, c : SequentA, a : Option[List[TermOccurrence]], p : Option[List[TermOccurrence]]) extends RuleA(tpe, c,a,p)
abstract case class BinaryRuleA(tpe: BinaryRuleTypeA, upper1 : RuleA, upper2 : RuleA, c: SequentA, a : Option[List[TermOccurrence]], p : Option[List[TermOccurrence]]) extends RuleA(tpe, c,a,p)
