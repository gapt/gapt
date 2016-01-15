package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ ProjectionFromEndSequent, Definition, Justification }
import at.logic.gapt.expr.hol.{ CNFn, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }

import scala.collection.mutable

object RobinsonToExpansionProof {

  def apply( p: ResolutionProof, es: HOLSequent,
             justifications: Set[( HOLClause, Justification )],
             definitions:    Map[HOLAtomConst, LambdaExpression] ): ExpansionSequent =
    expansionProofFromInstances( groundInstancesFromResolutionProof( p ), es, justifications, definitions )

  def apply( p: ResolutionProof, es: HOLSequent ): ExpansionSequent = {
    val justifications =
      for {
        ( f, i ) <- es.zipWithIndex.elements
        fs = if ( i isAnt ) f +: Sequent() else Sequent() :+ f
        clause <- CNFn.toFClauseList( fs.toFormula )
        pcnf = PCNF( fs, clause )
        exp = for ( ( e, ei ) <- LKToExpansionProof( pcnf ).zipWithIndex if ei sameSideAs i if toShallow( e ) == f ) yield e
        just = ProjectionFromEndSequent( exp, i )
      } yield clause -> just
    apply( p, es, justifications toSet, Map() )
  }

  def apply( p: ResolutionProof ): ExpansionSequent =
    ( for ( ( clause, substs ) <- groundInstancesFromResolutionProof( p ) )
      yield formulaToExpansionTree( univclosure( clause.toFormula ), substs.toList, pos = false ) ) ++: Sequent()
}

object expansionProofFromInstances {
  def apply[S <: Substitution]( substs: Map[HOLClause, Set[S]], es: HOLSequent,
                                justifications: Set[( HOLClause, Justification )],
                                definitions:    Map[HOLAtomConst, LambdaExpression] ): ExpansionSequent = {
    // Here, we can perform merges locally since we don't have strong quantifier nodes and all
    // skolem constants are consistent.

    val defElim = DefinitionElimination( definitions.toMap )
    val defAtomExpansion = mutable.Map[( HOLAtom, Boolean ), ExpansionTreeWithMerges]()
    def elimDefs( et: ExpansionTreeWithMerges, pol: Boolean ): ExpansionTreeWithMerges = et match {
      case ETTop    => ETTop
      case ETBottom => ETBottom
      case ETAtom( atom @ Apps( abbrev: HOLAtomConst, args ) ) if definitions isDefinedAt abbrev =>
        lazy val shallow = defElim( atom )
        defAtomExpansion.getOrElseUpdate(
          atom -> pol,
          merge( ETMerge( for {
            ( clause, Definition( defAtom, expansionWithDefs ) ) <- justifications
            if substs isDefinedAt clause
            renaming <- syntacticMatching( defAtom, atom ).toSet[Substitution]
            expansion = elimDefs( expansionWithDefs, pol )
            subst <- substs( clause )
          } yield substitute( subst compose renaming, expansion ) ) getOrElse ETWeakening( shallow ) )
        )
      case ETAtom( _ )     => et
      case ETNeg( t1 )     => ETNeg( elimDefs( t1, !pol ) )
      case ETAnd( t1, t2 ) => ETAnd( elimDefs( t1, pol ), elimDefs( t2, pol ) )
      case ETOr( t1, t2 )  => ETOr( elimDefs( t1, pol ), elimDefs( t2, pol ) )
      case ETImp( t1, t2 ) => ETImp( elimDefs( t1, !pol ), elimDefs( t2, pol ) )
      case ETSkolemQuantifier( f, v, selection ) =>
        ETSkolemQuantifier( f, v, elimDefs( selection, pol ) )
      case ETWeakQuantifier( f, instances ) =>
        ETWeakQuantifier( f, instances map { case ( t, term ) => elimDefs( t, pol ) -> term } )
      case ETWeakening( f ) => ETWeakening( defElim( f ) )
    }

    for ( ( formula, idx ) <- es.zipWithIndex ) yield merge( ETMerge(
      for {
        ( clause, ProjectionFromEndSequent( projWithDefs, `idx` ) ) <- justifications
        if substs isDefinedAt clause
        proj = elimDefs( projWithDefs.elements.head, idx isSuc )
        subst <- substs( clause )
      } yield substitute( subst, proj )
    ) getOrElse ETWeakening( formula ) )
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
        case _ => node.immediateSubProofs flatMap getInst toSet
      } )

    getInst( p ).groupBy { _._1 }.mapValues { _.map { _._2 }.map { Substitution( _ ) } }
  }

}
