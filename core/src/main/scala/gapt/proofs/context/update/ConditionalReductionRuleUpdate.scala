package gapt.proofs.context.update

import gapt.expr.util.ConditionalReductionRule
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.ConditionalReductions

case class ConditionalReductionRuleUpdate( rs: Seq[ConditionalReductionRule] ) extends Update {
  override def apply( ctx: Context ): State = {
    ctx.state.update[ConditionalReductions]( _ ++ rs.toVector )
  }
}
object ConditionalReductionRuleUpdate {
  implicit def conditionalReductionRulesToUpdate( rs: Seq[ConditionalReductionRule] ): Update =
    ConditionalReductionRuleUpdate( rs )
}