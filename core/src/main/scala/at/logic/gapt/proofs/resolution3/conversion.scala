package at.logic.gapt.proofs.resolution3
import at.logic.gapt.proofs.{ resolution => old }

import scala.collection.mutable

object resOld2New {
  def apply( p: old.ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[old.ResolutionProof, ResolutionProof]()

    def f( p: old.ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case old.InputClause( clause )     => Input( clause )
      case old.TautologyClause( atom )   => Taut( atom )
      case old.ReflexivityClause( term ) => Refl( term )
      case old.Instance( q, subst ) =>
        Subst( f( q ), subst )
      case old.Factor( q, i1, i2 ) =>
        val q_ = f( q )
        val Seq( j1, j2, _* ) = for ( ( a, j ) <- q_.conclusion.zipWithIndex.elements if a == q.conclusion( i1 ) if j sameSideAs i1 ) yield j
        Factor( q_, j1, j2 )
      case p @ old.Resolution( q1, i1, q2, i2 ) =>
        val q1_ = f( q1 )
        val q2_ = f( q2 )
        Resolution( q1_, q1_.conclusion.indexOfInSuc( q1.conclusion( i1 ) ),
          q2_, q2_.conclusion.indexOfInAnt( q2.conclusion( i2 ) ) )
      case p @ old.Paramodulation( q1, eq, q2, idx, ctx, ltr ) =>
        val q1_ = f( q1 )
        val q2_ = f( q2 )
        Paramod( q1_, q1_.conclusion.indexOfInSuc( q1.conclusion( eq ) ), ltr,
          q2_, q2_.conclusion.indexOfPol( q2.conclusion( idx ), idx.isSuc ),
          ctx )
    } )

    f( p )
  }
}