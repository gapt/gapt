package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._

object expansionProofFromInstances {
  def apply[S <: Substitution](
    substitutions:          Map[HOLClause, Set[S]],
    justifications:         Set[ResolutionProof],
    pureFOLwithoutEquality: Boolean                = false
  ): ExpansionProof = {
    require( substitutions.keySet.toSet[HOLSequent] subsetOf justifications.map( _.conclusion ) )

    val proofs = for {
      ( clause, substs ) <- substitutions
      just <- justifications
      if just.conclusion == clause
      subst <- substs
    } yield Subst( just, subst )

    var retSeq: ExpansionSequent = Sequent()
    val expansionWithDefs = ExpansionProofWithCut( Sequent( proofs.
      flatMapS( ResolutionToExpansionProof.withDefs( _, {
        case ( Input( Sequent( Seq( f ), Seq() ) ), expSeq, set ) if freeVariables( f ).isEmpty =>
          retSeq = expSeq
          retSeq :+= ETMerge( f, Polarity.InSuccedent, set.map( _._2.elements.head ) )
          retSeq

        case ( Input( Sequent( Seq(), Seq( f ) ) ), expSeq, set ) if freeVariables( f ).isEmpty =>
          retSeq = expSeq
          retSeq +:= ETMerge( f, Polarity.InAntecedent, set.map( _._2.elements.head ) )
          retSeq

        case ( Input( seq ), expSeq, set ) =>
          retSeq = expSeq
          val fvs = freeVariables( seq ).toSeq
          val sh = All.Block( fvs, seq.toDisjunction )
          retSeq +:= ETWeakQuantifierBlock( sh, fvs.size,
            for ( ( subst, es ) <- set ) yield subst( fvs ) -> es.toDisjunction( Polarity.Negative ) )
          retSeq
      }, addConclusion = false ).expansionWithCutAxiom.expansionSequent ).
      polarizedElements.groupBy( pe => pe._1.shallow -> pe._2 ).
      values.map( g => ETMerge( g.map( _._1 ) ) -> g.head._2 ).toSeq ) )

    val defConsts = expansionWithDefs.expansionWithCutAxiom.atomDefs.keySet
    eliminateCutsET( eliminateDefsET( eliminateCutsET( eliminateMerges( expansionWithDefs ) ), pureFOLwithoutEquality, defConsts ) )
  }
}