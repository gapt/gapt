package gapt.examples.sequence

import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.Imp
import gapt.expr.util.syntacticMatching
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.focus

trait ExplicitEqualityTactics {

  /**
   * Applies the quantified equation ∀x(e_l=e_r) to the left side of the equation tgt_l=tgt_r,
   * leaving open the subgoal e_r σ = tgt_r.
   */
  def explicitRewriteLeft(
    equation: String, targetEq: String,
    transitivity: String = "trans" ) =
    for {
      goal <- currentGoal
      All.Block( Seq( _, transVar, _ ), _ ) = goal( transitivity )
      All.Block( _, Imp.Block( _, Eq( eqL, eqR ) ) ) = goal( equation )
      Eq( tgtL, tgtR ) = goal( targetEq )
      subst <- syntacticMatching( eqL, tgtL ).
        toTactic( s"cannot match equation $equation to formula $targetEq" )
      _ <- chain( transitivity ).at( targetEq ).subst( transVar -> subst( eqR ) )
      _ <- chain( equation ).at( targetEq )
    } yield ()

  /**
   * Applies the quantified equation ∀x(e_l=e_r) to the right side of the equation tgt_l=tgt_r,
   * leaving open the subgoal tgt_l = e_l σ.
   */
  def explicitRewriteRight(
    equation: String, targetEq: String,
    transitivity: String = "trans" ) =
    for {
      goal <- currentGoal
      All.Block( Seq( _, transVar, _ ), _ ) = goal( transitivity )
      All.Block( _, Imp.Block( _, Eq( eqL, eqR ) ) ) = goal( equation )
      Eq( tgtL, tgtR ) = goal( targetEq )
      subst <- syntacticMatching( eqR, tgtR ).
        toTactic( s"cannot match equation $equation to formula $targetEq" )
      _ <- chain( transitivity ).at( targetEq ).subst( transVar -> subst( eqL ) )
      _ <- focus( 1 )
      _ <- chain( equation ).at( targetEq )
    } yield ()

}
