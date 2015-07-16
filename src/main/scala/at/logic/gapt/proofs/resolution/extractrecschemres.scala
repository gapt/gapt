package at.logic.gapt.proofs.resolution.robinson

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.resolution._

object extractRecSchemFromResProof {
  def apply( p: RobinsonResolutionProof ): ( RecursionScheme, InstanceTermEncoding ) = {
    val endSequent = HOLSequent( initialSequents( p ).map( _.toFormula ).map( univclosure( _ ) ).toSeq, Seq() )
    val encoding = new InstanceTermEncoding( endSequent )
    apply( p, clause => encoding.encodeOption( clause.toFormula.asInstanceOf[FOLFormula] -> true ) ) -> encoding
  }

  def apply( root: RobinsonResolutionProof, clauseTerm: HOLClause => Option[FOLTerm] ): RecursionScheme = {
    val nodeMap = root.nodes.zipWithIndex.map {
      case ( p: RobinsonResolutionProof, i ) =>
        val fvs = freeVariables( p.root.toFormula.asInstanceOf[FOLFormula] )
        p -> FOLFunction( s"B$i", fvs.toSeq )
    }.toMap
    val rules = nodeMap.flatMap {
      case ( InitialClause( clause ), nt ) =>
        clauseTerm( clause.toHOLClause ).map { term => Rule( nt, term ) }.toSeq
      case ( Factor( clause, p1, List( occurrences ), subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ) )
      case ( Variant( clause, p1, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ) )
      case ( Instance( clause, p1, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ) )
      case ( Resolution( clause, p1, p2, occ1, occ2, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ), Rule( nt, subst( nodeMap( p2 ) ) ) )
      case ( Paramodulation( clause, p1, p2, occ1, occ2, main, subst ), nt ) =>
        Seq( Rule( nt, subst( nodeMap( p1 ) ) ), Rule( nt, subst( nodeMap( p2 ) ) ) )
    }
    RecursionScheme( rules.toSet + Rule( FOLFunction( "A" ), nodeMap( root ) ) )
  }
}