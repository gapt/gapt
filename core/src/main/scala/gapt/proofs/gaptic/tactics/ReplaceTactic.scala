package gapt.proofs.gaptic.tactics

import gapt.expr.Expr
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.HOLPosition
import gapt.proofs.SequentIndex
import gapt.proofs.context.Context
import gapt.proofs.gaptic.OnLabel
import gapt.proofs.gaptic.OpenAssumption
import gapt.proofs.gaptic.Tactic
import gapt.proofs.gaptic.TacticFailureException
import gapt.proofs.gaptic.Tactical1
import gapt.proofs.lk.rules.ConversionRule

/**
 * Replaces all occurrences of a given term another term.
 *
 * @param target The label of the formula in which to replace the terms.
 * @param u The term to be replaced.
 * @param v The term by which u is replaced.
 * @param ctx A context.
 */
case class ReplaceTactic( target: String, u: Expr, v: Expr )( implicit ctx: Context ) extends Tactical1[Unit] {

  private def convert( formula: Formula ): Formula = {
    formula.find( u ).foldLeft[Expr]( formula ) {
      case ( f: Expr, p: HOLPosition ) => f.replace( p, v )
    }.asInstanceOf[Formula]
  }

  /**
   * Constructs a "replace" tactic.
   *
   * The method fails if the given goal does not contain the label `target` or if the terms `u` and `v` are not
   * definitionally equal in the context `ctx`.
   *
   * @param goal A goal.
   * @return A tactic that replaces the given goal by a goal in which the formula indicated by the label target is
   * replaced by the formula obtained by replacing all occurrences of the term u by the term v.
   */
  override def apply( goal: OpenAssumption ): Tactic[Unit] = {

    if ( !ctx.isDefEq( u, v ) )
      throw new TacticFailureException( s"expressions $u and $v are not definitionally equal" )

    for {
      ( label: String, main: Formula, idx: SequentIndex ) <- findFormula( goal, OnLabel( target ) )
      newGoal = OpenAssumption( goal.labelledSequent.updated( idx, label -> convert( main ) ) )
      _ <- replace( ConversionRule( newGoal, idx, main ) )
    } yield ()
  }

}
