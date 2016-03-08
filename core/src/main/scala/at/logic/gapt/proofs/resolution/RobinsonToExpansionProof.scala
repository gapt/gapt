package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ ProjectionFromEndSequent, Definition, Justification }
import at.logic.gapt.expr.hol.{ CNFp, instantiate, CNFn, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

object RobinsonToExpansionProof {

  def apply( p: ResolutionProof, es: HOLSequent,
             justifications: Map[HOLClause, Justification],
             definitions:    Map[HOLAtomConst, LambdaExpression] ): ExpansionProof =
    expansionProofFromInstances( groundInstancesFromResolutionProof( p ), es, justifications, definitions,
      pureFOLwithoutEquality = !containsEquationalReasoning( p ) )

  def apply( p: ResolutionProof, es: HOLSequent ): ExpansionProof = {
    val justifications =
      for {
        ( f, i ) <- es.zipWithIndex.elements
        fs = if ( i isAnt ) f +: Sequent() else Sequent() :+ f
        clause <- CNFn.toFClauseList( fs.toFormula )
        pcnf = PCNF( fs, clause )
        exp = for {
          ( e, ei ) <- LKToExpansionProof( pcnf ).toExpansionProof.expansionSequent.zipWithIndex
          if ei sameSideAs i
          if e.shallow == f
        } yield e
        just = ProjectionFromEndSequent( exp, i )
      } yield clause -> just
    apply( p, es, justifications.toMap, Map() )
  }

  def apply( p: ResolutionProof ): ExpansionProof =
    apply( p, p.inputClauses.map { _.toFormula }.map { univclosure( _ ) } ++: Sequent() )
}

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
      ( clause, Definition( defAtom @ Apps( `defConst`, vs ), expansion ) ) <- justifications
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
      definitions.keySet
    ) )

  }
}

object groundInstancesFromResolutionProof {

  def apply( p: ResolutionProof ): Map[HOLClause, Set[Substitution]] = {
    val substMap = mutable.Map[ResolutionProof, Set[( HOLClause, Map[Var, LambdaExpression] )]]()

    def getInst( node: ResolutionProof ): Set[( HOLClause, Map[Var, LambdaExpression] )] =
      substMap.getOrElseUpdate( node, node match {
        case InputClause( clause ) =>
          Set( clause -> freeVariables( clause ).map { v => v -> v }.toMap[Var, LambdaExpression] )
        case Instance( subProof, subst ) =>
          getInst( subProof ) map {
            case ( clause, instSubst ) =>
              clause -> instSubst.mapValues { subst( _ ) }
          }
        case node @ Splitting( splittingClause, part1, part2, case1, case2 ) =>
          val addInstFrom1 = getInst( case1 ) filter { inst => node.addInputClauses1 contains inst._1 } map { _._2 }
          val addInstFrom2 = getInst( case2 ) filter { inst => node.addInputClauses2 contains inst._1 } map { _._2 }
          val addInstances = for {
            subst1 <- addInstFrom1
            subst2 <- addInstFrom2
            subst = Substitution( subst1 ++ subst2 )
            ( cls, inst ) <- getInst( splittingClause )
          } yield cls -> inst.mapValues { subst( _ ) }
          val inst1 = getInst( case1 ).filterNot { inst => node.addInputClauses1 contains inst._1 }
          val inst2 = getInst( case2 ).filterNot { inst => node.addInputClauses2 contains inst._1 }
          inst1 union inst2 union addInstances
        case _ => node.immediateSubProofs flatMap getInst toSet
      } )

    getInst( p ).groupBy { _._1 }.mapValues { _.map { _._2 }.map { Substitution( _ ) } }
  }

}
