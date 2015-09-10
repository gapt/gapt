package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.existsclosure
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.{ Sequent, FOLClause }
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding

object extractRecSchemFromResProof {
  def apply( p: ResolutionProof ): ( RecursionScheme, InstanceTermEncoding ) = {
    val endSequent = existsclosure( Top() +: inputClauses( p ).map( _.toFormula ) ++: Sequent() )
    val encoding = new InstanceTermEncoding( endSequent )
    apply( p, encoding.encode( Top() -> true ),
      clause => encoding.encodeOption( clause.toFormula.asInstanceOf[FOLFormula] -> true ) ) -> encoding
  }

  def apply( root: ResolutionProof, emptyTerm: FOLTerm, clauseTerm: FOLClause => Option[FOLTerm] ): RecursionScheme = {
    val nodeMap = root.dagLikePostOrder.reverse.zipWithIndex.map {
      case ( p, i ) =>
        val fvs = freeVariables( p.conclusion )
        p -> FOLFunction( s"B$i", fvs.toSeq )
    }.toMap
    val rules = nodeMap.flatMap {
      case ( InputClause( clause ), nt ) =>
        clauseTerm( clause ).map { term => Rule( nt, term ) }.toSeq
      case ( Instance( p1, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ) )
      case ( p, nt ) if p.immediateSubProofs.isEmpty =>
        Seq( Rule( nt, emptyTerm ) )
      case ( p, nt ) if p.immediateSubProofs.nonEmpty =>
        p.immediateSubProofs map { sp => Rule( nt, nodeMap( sp ) ) }
    }
    RecursionScheme( rules.toSet + Rule( FOLFunction( "A" ), nodeMap( root ) ) )
  }
}