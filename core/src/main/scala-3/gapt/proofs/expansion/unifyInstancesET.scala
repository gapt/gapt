package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.syntacticMGU

/** Decreases the number of instances in an expansion proof by unifying the instance terms. */
object unifyInstancesET {
  def apply( ep: ExpansionProof ): ExpansionProof = {
    val instances = for ( case ETWeakQuantifier( _, insts ) <- ep.subProofs.toSeq ) yield insts.keySet

    // TODO: this is not enough to ensure acyclicity
    val subst = unifyInstances( instances, ep.eigenVariables ++ freeVariables( ep.shallow ) )

    if ( subst.isIdentity ) ep
    else apply( eliminateMerges( subst( ep ) ) )
  }

  private def unifyInstances( instances: Seq[Set[Expr]], forbiddenVariables: Set[Var] ): Substitution = {
    val nameGen = rename.awayFrom( containedNames( instances ) )
    val grounding = forbiddenVariables.map( ev => ev -> Const( nameGen.fresh( ev.name ), ev.ty ) )
    TermReplacement( unifyInstances( TermReplacement( instances, grounding.toMap ) ), grounding.map( _.swap ).toMap )
  }

  private def unifyInstances( instances: Seq[Set[Expr]] ): Substitution = scala.util.boundary {
    for {
      group <- instances
      ( a, i ) <- group.zipWithIndex
      ( b, j ) <- group.zipWithIndex
      if i < j
      mgu <- syntacticMGU( a, b )
    } scala.util.boundary.break(unifyInstances( mgu( instances ) ) compose mgu)

    Substitution()
  }

}
