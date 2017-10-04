package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr.Expr
import at.logic.gapt.grammars.RecursionScheme
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.{ Context, HOLSequent }

trait SchematicInductiveProofFindingMethod {
  def find( endSequent: HOLSequent, encoding: InstanceTermEncoding, context: Context,
            taggedLanguage: Set[( Seq[Expr], Expr )] ): SchematicProofWithInduction
}

trait InductiveGrammarFindingMethod extends SchematicInductiveProofFindingMethod {
  def findRS( taggedLanguage: Set[( Seq[Expr], Expr )] ): RecursionScheme

  override def find( endSequent: HOLSequent, encoding: InstanceTermEncoding, context: Context,
                     taggedLanguage: Set[( Seq[Expr], Expr )] ): SchematicProofWithInduction = {
    val rs = encoding.decode( findRS( taggedLanguage ) )
    ProofByRecursionScheme( endSequent, rs, context )
  }
}
