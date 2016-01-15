package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.existsclosure
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.{ HOLClause, Sequent, FOLClause }
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding

object extractRecSchemFromResProof {
  def apply( p: ResolutionProof ): ( RecursionScheme, InstanceTermEncoding ) = {
    val endSequent = existsclosure( inputClauses( p ).map( _.toFormula ) ++: Sequent() )
    val encoding = InstanceTermEncoding( endSequent )
    apply(
      p,
      clause => encoding.encodeOption( -clause.toFormula )
    ) -> encoding
  }

  def apply( root: ResolutionProof, clauseTerm: HOLClause => Option[LambdaExpression] ): RecursionScheme = {
    val nodeMap = root.dagLike.postOrder.reverse.zipWithIndex.map {
      case ( p, i ) =>
        val fvs = freeVariables( p.conclusion ).toSeq
        val nonTerminal = Const( s"B$i", FunctionType( Ti, fvs.map( _.exptype ) ) )
        p -> nonTerminal( fvs: _* )
    }.toMap
    val rules = nodeMap.flatMap {
      case ( InputClause( clause ), nt ) =>
        clauseTerm( clause ).map { term => Rule( nt, term ) }.toSeq
      case ( Instance( p1, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ) )
      case ( p, nt ) =>
        p.immediateSubProofs map { sp => Rule( nt, nodeMap( sp ) ) }
    }
    val axiom = FOLConst( "A" )
    RecursionScheme(
      axiom,
      nodeMap map { case ( _, Apps( nonTerminal: Const, _ ) ) => nonTerminal } toSet,
      rules.toSet + Rule( axiom, nodeMap( root ) )
    )
  }
}