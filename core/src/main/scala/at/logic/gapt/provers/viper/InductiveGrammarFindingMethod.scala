package at.logic.gapt.provers.viper

import at.logic.gapt.expr.LambdaExpression
import at.logic.gapt.grammars.RecursionScheme
import at.logic.gapt.proofs.{ FiniteContext, HOLSequent }
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

trait SchematicInductiveProofFindingMethod {
  def find( endSequent: HOLSequent, encoding: InstanceTermEncoding, context: FiniteContext,
            taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): SchematicProofWithInduction
}

trait InductiveGrammarFindingMethod extends SchematicInductiveProofFindingMethod {
  def findRS( taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): RecursionScheme

  override def find( endSequent: HOLSequent, encoding: InstanceTermEncoding, context: FiniteContext,
                     taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): SchematicProofWithInduction = {
    val rs = encoding.decode( findRS( taggedLanguage ) )
    val homogenized = homogenizeRS( rs )( context )
    ProofByRecursionScheme( endSequent, homogenized, context )
  }
}
