package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ ProjectionFromEndSequent, Definition, Justification }
import at.logic.gapt.expr.hol.{ instantiate, CNFn, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ DefinitionElimination, LKToExpansionProof }

import scala.collection.mutable

object RobinsonToExpansionProof {

  def apply( p: ResolutionProof, es: HOLSequent,
             justifications: Set[( HOLClause, Justification )],
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
          if toShallow( e ) == f
        } yield e
        just = ProjectionFromEndSequent( exp, i )
      } yield clause -> just
    apply( p, es, justifications toSet, Map() )
  }

  def apply( p: ResolutionProof ): ExpansionProof =
    apply( p, inputClauses( p ).map { _.toFormula }.map { univclosure( _ ) } ++: Sequent() )
}

/** Requires unipolar definitions. */
object expansionProofFromInstances {
  // In the case without equality, whenever we encounter a defined atom in an expansion of the end-sequent, we can
  // insert at that point all the expansions from the defining clauses where the defined atom matches literally.
  //
  // We can think of this operation as ad-hoc resolving the clauses from the end-sequent with the clauses from the
  // definitions.  This is sound since we only have unipolar definitions (and ground resolution).
  //
  // With equality however, you can resolve literals that are not literally equal.  In this case we want to insert
  // *all* the expansions from the defining clauses, even if they do not match.  To make this possible, we change the
  // instances of the clauses from the definitions to match the ones from the end-sequent, "mating" them.
  private def mateInstances( substs: Map[HOLClause, Set[Substitution]], justifications: Set[( HOLClause, Justification )] ): Map[HOLClause, Set[Substitution]] = {
    val todo = mutable.Set[( HOLClause, Substitution )]()

    for {
      ( defClause, Definition( defAtom @ Apps( defAtomC: HOLAtomConst, defArgs ), _ ) ) <- justifications
      if substs isDefinedAt defClause
      ( useClause, useSubsts ) <- substs
      if useClause != defClause
      Apps( `defAtomC`, useArgs ) <- useClause.elements
      defSubst <- substs( defClause )
      useSubst <- useSubsts
      newDefSubst = Substitution( defSubst.map ++ ( defArgs.map { _.asInstanceOf[Var] } zip ( useArgs map { useSubst( _ ) } ) ) )
      if !substs( defClause ).contains( newDefSubst )
    } todo += ( defClause -> newDefSubst )

    if ( todo isEmpty )
      substs
    else
      mateInstances(
        for ( ( clause, clauseSubsts ) <- substs )
          yield clause -> ( clauseSubsts union todo.filter { _._1 == clause }.map { _._2 } ),
        justifications
      )
  }

  def apply[S <: Substitution]( substitutions: Map[HOLClause, Set[S]], es: HOLSequent,
                                justifications:         Set[( HOLClause, Justification )],
                                definitions:            Map[HOLAtomConst, LambdaExpression],
                                pureFOLwithoutEquality: Boolean                             = false ): ExpansionProof = {

    val substs = if ( !pureFOLwithoutEquality && definitions.nonEmpty )
      mateInstances( substitutions mapValues { _.toSet }, justifications )
    else
      substitutions

    val defElim = DefinitionElimination( definitions.toMap )
    val defAtomExpansion = mutable.Map[( HOLAtom, Boolean ), ExpansionTree]()
    def elimDefs( et: ExpansionTree, shallow: HOLFormula ): ExpansionTree = ( et, shallow ) match {
      case ( ETTop( pol ), _ )    => ETTop( pol )
      case ( ETBottom( pol ), _ ) => ETBottom( pol )
      case ( ETAtom( atom @ Apps( abbrev: HOLAtomConst, args ), pol ), _ ) if definitions isDefinedAt abbrev =>
        defAtomExpansion.getOrElseUpdate(
          atom -> pol,
          ETMerge( ( for {
            ( clause, Definition( defAtom, expansionWithDefs ) ) <- justifications
            if substs isDefinedAt clause
            subst <- substs( clause )
            if subst( defAtom ) == atom
          } yield elimDefs( subst( expansionWithDefs ), shallow ) ) + ETWeakening( shallow, pol ) )
        )
      case ( ETAtom( _, _ ), _ )                => et
      case ( ETNeg( t1 ), Neg( sh1 ) )          => ETNeg( elimDefs( t1, sh1 ) )
      case ( ETAnd( t1, t2 ), And( sh1, sh2 ) ) => ETAnd( elimDefs( t1, sh1 ), elimDefs( t2, sh2 ) )
      case ( ETOr( t1, t2 ), Or( sh1, sh2 ) )   => ETOr( elimDefs( t1, sh1 ), elimDefs( t2, sh2 ) )
      case ( ETImp( t1, t2 ), Imp( sh1, sh2 ) ) => ETImp( elimDefs( t1, sh1 ), elimDefs( t2, sh2 ) )
      case ( ETSkolemQuantifier( f, st, selection ), _ ) =>
        ETSkolemQuantifier( shallow, st, elimDefs( selection, instantiate( shallow, st ) ) )
      case ( ETWeakQuantifier( f, instances ), _ ) =>
        ETWeakQuantifier( shallow, for ( ( term, inst ) <- instances ) yield term -> elimDefs( inst, instantiate( shallow, term ) ) )
      case ( ETWeakening( f, pol ), _ ) => ETWeakening( shallow, pol )
    }

    eliminateMerges( ExpansionProof(
      for ( ( formula, idx ) <- es.zipWithIndex ) yield ETMerge(
        ( for {
          ( clause, ProjectionFromEndSequent( projWithDefs, `idx` ) ) <- justifications
          if substs isDefinedAt clause
          subst <- substs( clause )
        } yield elimDefs( subst( projWithDefs.elements.head ), formula ) )
          + ETWeakening( formula, idx isSuc )
      )
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
        case _ => node.immediateSubProofs flatMap getInst toSet
      } )

    getInst( p ).groupBy { _._1 }.mapValues { _.map { _._2 }.map { Substitution( _ ) } }
  }

}
