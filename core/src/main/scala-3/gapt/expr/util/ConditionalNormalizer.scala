package gapt.expr.util

import gapt.expr.Expr
import gapt.expr.Normalizer
import gapt.expr.ReductionRule
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.formats.tip.subterms

case class ConditionalNormalizer(rewriteRules: Set[ConditionalReductionRule]) {

  private val unconditionalRules =
    rewriteRules
      .filter { _.conditions.isEmpty }
      .map { r => ReductionRule(r.lhs, r.rhs) }

  private val conditionalRules = rewriteRules.diff(rewriteRules.filter { _.conditions.isEmpty })

  private val unconditionalNormalizer = Normalizer(unconditionalRules)

  /**
   * Normalizes an expression.
   *
   * @param e The expression to be normalized.
   * @return Returns the normalized expression, if the rewrite rules are terminating.
   */
  def normalize(e: Expr): Expr = {
    normalize_(unconditionalNormalizer.normalize(e))
  }

  private def normalize_(e: Expr): Expr = scala.util.boundary {
    for {
      ConditionalReductionRule(conditions, lhs, rhs) <- conditionalRules
      (instance, position) <- findInstances(e, lhs, Nil)
    } {
      if (conditions.map { instance(_) }.map { normalize(_) }.forall { _ == Top() }) {
        scala.util.boundary.break(normalize(e.replace(position, instance(rhs))))
      }
    }
    e
  }

  private def findInstances(e: Expr, l: Expr, position: List[Int]): Set[(Substitution, LambdaPosition)] = {
    subterms(e).flatMap {
      case (t, p) =>
        for {
          subst <- syntacticMatching(l, t)
        } yield { subst -> p }
    }.toSet
  }
}
