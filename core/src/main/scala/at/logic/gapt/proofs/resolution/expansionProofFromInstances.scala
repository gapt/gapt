package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._

object expansionProofFromInstances {
  def apply[S <: Substitution](
    substitutions:          Map[HOLClause, Set[S]],
    justifications:         Set[ResolutionProof],
    pureFOLwithoutEquality: Boolean                = false ): ExpansionProof = {
    require( substitutions.keySet.toSet[HOLSequent] subsetOf justifications.map( _.conclusion ) )

    val proofs = for {
      ( clause, substs ) <- substitutions
      just <- justifications
      if just.conclusion == clause
      subst <- substs
    } yield Subst( just, subst )

    val expansionWithDefs = ExpansionProof( Sequent( proofs.
      flatMapS( ResolutionToExpansionProof.withDefs( _, ResolutionToExpansionProof.inputsAsExpansionSequent, addConclusion = false ).expansionSequent ).
      polarizedElements.groupBy( pe => pe._1.shallow -> pe._2 ).
      values.map( g => ETMerge( g.map( _._1 ) ) -> g.head._2 ).toSeq ) )

    eliminateCutsET( eliminateDefsET( eliminateCutsET( eliminateMerges( expansionWithDefs ) ), pureFOLwithoutEquality ) )
  }
}