package at.logic.gapt.proofs

import at.logic.gapt.expr._

import scala.collection.mutable

package object resolution {
  implicit object resolutionProofsAreReplaceable extends ClosedUnderReplacement[ResolutionProof] {
    def replace( proof: ResolutionProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): ResolutionProof = {

      val memo = mutable.Map[ResolutionProof, ResolutionProof]()

      def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
        case InputClause( clause )     => InputClause( TermReplacement( clause, repl ).map( _.asInstanceOf[HOLAtom] ) )
        case ReflexivityClause( term ) => ReflexivityClause( TermReplacement( term, repl ) )
        case TautologyClause( atom )   => TautologyClause( TermReplacement( atom, repl ).asInstanceOf[HOLAtom] )
        case Factor( q, i1, i2 )       => Factor( f( q ), i1, i2 )
        case Instance( q, subst ) =>
          Instance( f( q ), Substitution( subst.map.map { case ( f, t ) => f -> TermReplacement( t, repl ) } ) )
        case Resolution( q1, l1, q2, l2 ) => Resolution( f( q1 ), l1, f( q2 ), l2 )
        case Paramodulation( q1, l1, q2, l2, con, dir ) =>
          val q1New = f( q1 )
          val q2New = f( q2 )
          val ( equation, auxFormula ) = ( q1New.conclusion( l1 ), q2New.conclusion( l2 ) )
          val Abs( v, subContext ) = con
          val v_ = rename( v, freeVariables( equation ) ++ freeVariables( auxFormula ) )
          val contextNew = Abs( v_, TermReplacement( Substitution( v, v_ )( subContext ), repl ) )
          Paramodulation( q1New, l1, q2New, l2, contextNew, dir )
        case Splitting( q0, c1, c2, q1, q2 ) =>
          Splitting(
            f( q0 ),
            TermReplacement( c1, repl ).map( _.asInstanceOf[HOLAtom] ),
            TermReplacement( c2, repl ).map( _.asInstanceOf[HOLAtom] ),
            f( q1 ), f( q2 )
          )
      } )

      f( proof )
    }
  }
}
