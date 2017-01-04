package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._

/** Decreases the number of instances in an expansion proof by unifying the instance terms. */
object unifyInstancesET {
  def apply( epwc: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( apply( epwc.expansionWithCutAxiom ) )

  def apply( ep: ExpansionProof ): ExpansionProof = {
    val instances = for ( ETWeakQuantifier( _, insts ) <- ep.subProofs.toSeq ) yield insts.keySet

    val subst = unifyInstances( instances, ep.eigenVariables ++ freeVariables( ep.shallow ) )

    if ( subst.isIdentity ) ep
    else apply( eliminateMerges( subst( ep ) ) )
  }

  private def unifyInstances( instances: Seq[Set[LambdaExpression]], forbiddenVariables: Set[Var] ): Substitution = {
    val nameGen = rename.awayFrom( containedNames( instances ) )
    val grounding = forbiddenVariables.map( ev => ev -> Const( nameGen.fresh( ev.name ), ev.exptype ) )
    TermReplacement( unifyInstances( TermReplacement( instances, grounding.toMap ) ), grounding.map( _.swap ).toMap )
  }

  private def unifyInstances( instances: Seq[Set[LambdaExpression]] ): Substitution = {
    for {
      group <- instances
      ( a, i ) <- group.zipWithIndex
      ( b, j ) <- group.zipWithIndex
      if i < j
      mgu <- syntacticMGU( a, b )
    } return unifyInstances( mgu( instances ) ) compose mgu

    Substitution()
  }

}
