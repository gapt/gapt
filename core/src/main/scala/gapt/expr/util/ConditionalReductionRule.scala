package gapt.expr.util

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ReductionRule
import gapt.expr.Var
import gapt.expr.formula.Formula

/**
 * A conditional rewrite rule.
 *
 * An instance of this rule can be used to rewrite the left hand side
 * into its right hand side only if the conditions all rewrite to ⊤.
 *
 * The free variables of the conditions together with those of the
 * right hand side must form a subset of the free variables of the
 * left hand side. The left hand side must not be a variable.
 *
 * @param conditions The conditions of this rewrite rule.
 * @param lhs The left hand side of this rewrite rule.
 * @param rhs The right hand side of this rewrite rule.
 */
case class ConditionalReductionRule(conditions: Seq[Formula], lhs: Expr, rhs: Expr) {

  require(
    (conditions.flatMap { freeVariables(_) } ++
      freeVariables(rhs)).toSet.subsetOf(freeVariables(lhs)),
    """free variables in conditions and right hand side do not form a
      |subset of the free variables of the left hand side""".stripMargin
  )

  require(!lhs.isInstanceOf[Var], "left hand side must not be a variable")

  val Apps(lhsHead @ Const(lhsHeadName, _, _), lhsArgs) = lhs: @unchecked
  val lhsArgsSize: Int = lhsArgs.size
}

object ConditionalReductionRule {
  def apply(rule: ReductionRule): ConditionalReductionRule =
    ConditionalReductionRule(List(), rule.lhs, rule.rhs)
}
