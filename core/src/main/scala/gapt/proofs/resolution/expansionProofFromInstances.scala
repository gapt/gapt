package gapt.proofs.resolution

import gapt.expr._
import gapt.proofs._
import gapt.proofs.expansion._
import gapt.utils.Maybe

object expansionProofFromInstances {
  def apply[S <: Substitution](
    substitutions:          Map[HOLClause, Set[S]],
    justifications:         Set[ResolutionProof],
    pureFOLwithoutEquality: Boolean                = false )( implicit ctx: Maybe[Context] ): ExpansionProof = {
    require( substitutions.keySet.toSet[HOLSequent] subsetOf justifications.map( _.conclusion ) )

    val proofs = for {
      ( clause, substs ) <- substitutions
      just <- justifications
      if just.conclusion == clause
      subst <- substs
    } yield Subst( just, subst )

    implicit val ctx1: Context = ctx.getOrElse( MutableContext.guess( proofs ) )

    val expansionWithDefs = ExpansionProof( ETMerge( proofs.
      flatMapS( ResolutionToExpansionProof.withDefs(
        _,
        ResolutionToExpansionProof.inputsAsExpansionSequent, addConclusion = false ).
        expansionSequent ) ) )

    eliminateCutsET( eliminateDefsET( eliminateCutsET( eliminateMerges( expansionWithDefs ) ), pureFOLwithoutEquality ) )
  }
}