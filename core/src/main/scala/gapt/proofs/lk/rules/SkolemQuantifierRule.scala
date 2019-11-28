package gapt.proofs.lk.rules

import gapt.expr.Apps
import gapt.expr.BetaReduction
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Var
import gapt.expr.hol.instantiate
import gapt.proofs.SequentIndex

trait SkolemQuantifierRule extends UnaryLKProof with CommonRule {
  def aux: SequentIndex
  def mainFormula: Formula
  def skolemTerm: Expr

  //  require( freeVariables( skolemDef ).isEmpty )

  val ( auxFormula, context ) = premise focus aux

  def quantifiedVariable: Var
  def subFormula: Formula

  val Apps( skolemConst: Const, skolemArgs ) = skolemTerm

  //  {
  //    val expectedMain = BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) )
  //    if ( expectedMain != mainFormula )
  //      throw LKRuleCreationException( s"Main formula should be $expectedMain, but is $mainFormula" )
  //  }

  {
    val expectedAux = BetaReduction.betaNormalize( instantiate( mainFormula, skolemTerm ) )
    if ( expectedAux != auxFormula )
      throw LKRuleCreationException(
        s"Aux formula should be $subFormula[$quantifiedVariable\\$skolemTerm] = $expectedAux, but is $auxFormula." )
  }
}
