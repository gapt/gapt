package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.structuralCNF.{ ProjectionFromEndSequent, Definition, Justification }
import at.logic.gapt.expr.hol.{ containsQuantifierOnLogicalLevel, CNFn, univclosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew.{ DefinitionElimination, LKToExpansionProof }

import scala.collection.mutable

object RobinsonToExpansionProof {

  def apply( p: ResolutionProof, es: HOLSequent, justifications: Set[( HOLClause, Justification )], definitions: Map[HOLAtomConst, LambdaExpression] ): ExpansionSequent = {
    def elimDefs( et: ExpansionTree, pol: Boolean ): ExpansionTree = et match {
      case ETTop    => ETTop
      case ETBottom => ETBottom
      case ETAtom( atom @ Apps( abbrev: HOLAtomConst, args ) ) if definitions isDefinedAt abbrev =>
        // The definitions that structuralCNF introduces are only ever used in one polarity.
        ETWeakening( DefinitionElimination( definitions.toMap[LambdaExpression, LambdaExpression], atom ) )
      case ETAtom( _ )     => et
      case ETNeg( t1 )     => ETNeg( elimDefs( t1, !pol ) )
      case ETAnd( t1, t2 ) => ETAnd( elimDefs( t1, pol ), elimDefs( t2, pol ) )
      case ETOr( t1, t2 )  => ETOr( elimDefs( t1, pol ), elimDefs( t2, pol ) )
      case ETImp( t1, t2 ) => ETImp( elimDefs( t1, !pol ), elimDefs( t2, pol ) )
      case ETStrongQuantifier( f, v, selection ) =>
        ETStrongQuantifier( f, v, elimDefs( selection, pol ) )
      case ETSkolemQuantifier( f, v, selection ) =>
        ETSkolemQuantifier( f, v, elimDefs( selection, pol ) )
      case ETWeakQuantifier( f, instances ) =>
        ETWeakQuantifier.applyWithoutMerge( f, instances map { case ( t, term ) => elimDefs( t, pol ) -> term } )
      case ETWeakening( f ) => ETWeakening( DefinitionElimination( definitions.toMap[LambdaExpression, LambdaExpression], f ) )
    }
    def elimDefsES( es: ExpansionSequent ): ExpansionSequent =
      es.map( elimDefs( _, false ), elimDefs( _, true ) )

    def getESProj( justification: Justification ): ExpansionSequent = justification match {
      case ProjectionFromEndSequent( projection, _ ) => projection
      case Definition( _, _, prevJust )              => getESProj( prevJust )
    }

    apply_( p, clause => {
      val fvs = freeVariables( clause ).toSeq
      for {
        ( `clause`, just ) <- justifications
        proj = getESProj( just )
      } yield ( ( subst: Seq[LambdaExpression] ) => elimDefsES( substitute( Substitution( fvs zip subst ), proj ) ) ) -> fvs.asInstanceOf[Seq[LambdaExpression]]
    } )
  }

  def apply( p: ResolutionProof, es: HOLSequent ): ExpansionSequent = {
    val justifications =
      for {
        ( f, i ) <- es.zipWithIndex.elements
        fs = if ( i isAnt ) f +: Sequent() else Sequent() :+ f
        clause <- CNFn.toFClauseList( fs.toFormula )
        pcnf = PCNF( fs, clause )
        exp = LKToExpansionProof( pcnf ) diff clause.map( ETAtom )
        just = ProjectionFromEndSequent( exp, i )
      } yield clause -> just
    apply( p, es, justifications toSet, Map() )
  }

  def apply( p: ResolutionProof ): ExpansionSequent =
    apply_( p, ( clause: HOLClause ) => {
      val fvs = freeVariables( clause ).toSeq
      val formula = univclosure( clause.toFormula )
      Set( ( ( subst: Seq[LambdaExpression] ) =>
        formulaToExpansionTree( formula, List( Substitution( fvs zip subst ) ), false ) +: Sequent() ) ->
        fvs )
    } )

  private def apply_(
    p:         ResolutionProof,
    instForIC: HOLClause => Set[( Seq[LambdaExpression] => ExpansionSequent, Seq[LambdaExpression] )]
  ): ExpansionSequent = {
    val inst = getInstances( p, instForIC )

    var ant = mutable.Buffer[ExpansionTree]()
    val suc = mutable.Buffer[ExpansionTree]()
    for ( ( esTransf, instSubst ) <- inst ) {
      val es = esTransf( instSubst )
      ant ++= es.antecedent
      suc ++= es.succedent
    }

    merge(
      ant.groupBy { toShallow( _ ) }.values.map { _.reduce( ETMerge ) }.toSeq,
      suc.groupBy { toShallow( _ ) }.values.map { _.reduce( ETMerge ) }.toSeq
    )
  }

  private def getInstances[T](
    p:         ResolutionProof,
    instForIC: HOLClause => Set[( T, Seq[LambdaExpression] )]
  ): Set[( T, Seq[LambdaExpression] )] = {
    val substMap = mutable.Map[ResolutionProof, Set[( T, Seq[LambdaExpression] )]]()

    def getInst( node: ResolutionProof ): Set[( T, Seq[LambdaExpression] )] =
      substMap.getOrElseUpdate( node, node match {
        case InputClause( clause ) =>
          instForIC( clause )
        case Instance( subProof, subst ) =>
          getInst( subProof ) map {
            case ( tag, instSubst ) =>
              tag -> instSubst.map { subst( _ ) }
          }
        case _ => node.immediateSubProofs flatMap getInst toSet
      } )

    getInst( p )
  }
}
