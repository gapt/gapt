package gapt.proofs.context

import gapt.expr.Eq
import gapt.expr.Expr
import gapt.expr.ReductionRule
import gapt.expr.preExpr
import gapt.formats.babel.BabelParser
import Context.Reductions
import Context.Update

class ReductionRuleUpdate(
    private val rules: Seq[ReductionRule] ) extends Update {

  /**
   * Adds reduction rules to a context.
   *
   * @param ctx The context to be updated.
   * @return A new context state which is obtained by the context's state
   * by appending the reduction rules saved in this update to the `Reductions`
   * facet.
   */
  override def apply( ctx: Context ): Context.State = {
    ctx.state.update[Reductions]( _ ++ rules.toVector )
  }
}

object ReductionRuleUpdate {

  /**
   * Converts a reduction rule to an update.
   *
   * @param rule The reduction rule to be converted.
   * @return A reduction rule update containing only the given reduction rule.
   */
  implicit def reductionRuleAsReductionRuleUpdate(
    rule: ReductionRule ): ReductionRuleUpdate = {

    new ReductionRuleUpdate( Seq( rule ) )
  }

  /**
   * Converts a sequence of reduction rules to an update.
   *
   * @param rules The reduction rules to be converted.
   * @return A reduction rule update containing only the given reduction rules.
   */
  implicit def reductionRulesAsReductionRuleUpdate(
    rules: Seq[ReductionRule] ): ReductionRuleUpdate = {

    new ReductionRuleUpdate( rules )
  }

  /**
   * Creates a reduction rule update.
   *
   * @param equations The strings to be interpreted as reduction rules. The
   * given strings must encode equations. The equations encoded by the given
   * strings are interpreted as reduction rules that operate from left to
   * right.
   * @param ctx The context under which the equations are decoded.
   * @return A reduction rule update containing exactly the reduction rules
   * encoded by the given strings.
   */
  def apply(
    equations: String* )( implicit ctx: Context ): ReductionRuleUpdate = {

    new ReductionRuleUpdate(
      equations.map { parseEquation( _ ) }.map { ReductionRule( _ ) } )
  }

  private def parseEquation(
    eqn: String )( implicit ctx: Context ): ( Expr, Expr ) = {

    BabelParser.tryParse( eqn, p => preExpr.TypeAnnotation( p, preExpr.Bool ) ).
      fold( throw _, identity ) match {
        case Eq( lhs, rhs ) => lhs -> rhs
        case _              => throw new IllegalArgumentException( "" )
      }
  }
}
