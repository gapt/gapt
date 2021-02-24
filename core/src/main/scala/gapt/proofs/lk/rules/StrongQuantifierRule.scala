package gapt.proofs.lk.rules

import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.{ BetaReduction, Var }
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

abstract class StrongQuantifierRule extends UnaryLKProof with CommonRule with Eigenvariable {
  val aux: SequentIndex
  val eigenVariable: Var
  val quantifiedVariable: Var
  val mainFormula: Formula

  if ( !subProof.endSequent.isDefinedAt( aux ) )
    throw LKRuleCreationException( s"Sequent ${subProof.endSequent} is not defined at index ${aux}." )

  val ( auxFormula, context ) = premise focus aux

  // eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  val subFormula: Formula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw LKRuleCreationException(
      s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = " +
        BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) +
        s", but is $auxFormula." )
}

object StrongQuantifierRule {
  def apply( p: LKProof, aux: SequentIndex, eigen: Var, quant: Var, isForall: Boolean ): StrongQuantifierRule =
    if ( isForall )
      ForallRightRule( p, aux, eigen, quant )
    else
      ExistsLeftRule( p, aux, eigen, quant )

  def apply( p: LKProof, main: Formula, eigen: Var, isForall: Boolean ): StrongQuantifierRule =
    if ( isForall )
      ForallRightRule( p, main, eigen )
    else
      ExistsLeftRule( p, main, eigen )

  def unapply( p: StrongQuantifierRule ): Option[( LKProof, SequentIndex, Var, Var, Boolean )] = p match {
    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, false ) )
    case ForallRightRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, true ) )
    case _ => None
  }
}
