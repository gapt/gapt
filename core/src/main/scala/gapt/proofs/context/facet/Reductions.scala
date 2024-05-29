package gapt.proofs.context.facet

import gapt.expr.Normalizer
import gapt.expr.ReductionRule
import gapt.expr.util.ConditionalNormalizer
import gapt.expr.util.ConditionalReductionRule

/** Definitional reductions. */
case class Reductions(normalizer: Normalizer) {
  def ++(rules: Vector[ReductionRule]): Reductions =
    copy(Normalizer(normalizer.rules ++ rules))

  def +(reductionRule: ReductionRule): Reductions =
    copy(normalizer + reductionRule)

  override def toString: String =
    normalizer.rules.map { case ReductionRule(lhs, rhs) => s"$lhs -> $rhs" }.mkString("\n")
}

object Reductions {
  implicit val reductionsFacet: Facet[Reductions] = Facet(Reductions(Normalizer(Set())))
}

case class ConditionalReductions(normalizer: ConditionalNormalizer) {
  def ++(rules: Vector[ConditionalReductionRule]): ConditionalReductions =
    copy(ConditionalNormalizer(normalizer.rewriteRules ++ rules))

  def +(conditionalReductionRule: ConditionalReductionRule): ConditionalReductions =
    copy(ConditionalNormalizer(normalizer.rewriteRules + conditionalReductionRule))

  override def toString: String =
    normalizer.rewriteRules.map { case ConditionalReductionRule(conds, lhs, rhs) => s"$conds => $lhs -> $rhs" }.mkString("\n")
}

object ConditionalReductions {
  implicit val conditionalReductionsFacet: Facet[ConditionalReductions] =
    Facet(ConditionalReductions(ConditionalNormalizer(Set())))
}
