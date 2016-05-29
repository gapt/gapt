package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ Justification, ProjectionFromEndSequent }
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

object expansionProofFromInstances {
  def apply[S <: Substitution](
    substs: Map[HOLClause, Set[S]], es: HOLSequent,
    justifications:         Map[HOLClause, Justification],
    definitions:            Map[HOLAtomConst, LambdaExpression],
    pureFOLwithoutEquality: Boolean                             = false
  ): ExpansionProof = {
    require( substs.keySet subsetOf justifications.keySet )

    val endSequentETs =
      for ( ( formula, idx ) <- es.zipWithIndex ) yield ETMerge(
        formula, idx isSuc,
        for {
          ( clause, ProjectionFromEndSequent( projWithDefs, `idx` ) ) <- justifications
          if substs isDefinedAt clause
          subst <- substs( clause )
        } yield subst( projWithDefs.elements.head )
      )

    val defETs = for ( ( defConst, definingFormula ) <- definitions ) yield for {
      ( clause, structuralCNF.Definition( defAtom @ Apps( `defConst`, vs ), expansion ) ) <- justifications
      if substs isDefinedAt clause
    } yield {
      val defET =
        if ( expansion.polarity )
          ETAnd(
            ETWeakening( defAtom --> expansion.shallow, false ),
            ETImp( expansion, ETAtom( defAtom, false ) )
          )
        else
          ETAnd(
            ETImp( ETAtom( defAtom, true ), expansion ),
            ETWeakening( expansion.shallow --> defAtom, false )
          )
      ETWeakQuantifierBlock(
        All.Block( vs.map { _.asInstanceOf[Var] }, defAtom <-> expansion.shallow ),
        vs.size, for ( subst <- substs( clause ) ) yield subst( vs -> defET )
      )
    }
    val mergedDefETs = defETs.filter { _.nonEmpty }.map { ETMerge( _ ) }.toSeq

    val expansionProofWithDef = eliminateMerges( ExpansionProof( mergedDefETs ++: endSequentETs ) )

    eliminateCutsET( eliminateDefsET(
      expansionProofWithDef,
      pureFOLwithoutEquality,
      definitions.keySet.toSet[Const]
    ) )

  }
}
