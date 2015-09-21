package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.FOLClause

import scala.collection.mutable

object simplifyResolutionProof {
  def apply( proof: ResolutionProof ): ResolutionProof = {
    val simplified = mutable.Map[FOLClause, ResolutionProof]()

    proof dagLikeForeach { p =>
      val q = p match {
        case _: InitialClause => Factor( p )._1
        case Instance( p1, subst1 ) => simplified( p1.conclusion ) match {
          case Instance( q2, subst2 )    => Factor( Instance( q2, subst1 compose subst2 ) )._1
          case TautologyClause( atom )   => TautologyClause( subst1( atom ) )
          case ReflexivityClause( term ) => ReflexivityClause( subst1( term ) )
          case q1                        => Factor( Instance( q1, subst1 ) )._1
        }
        case Factor( p1, i1, j1 ) => simplified( p1.conclusion )
        case Resolution( p1, i1, p2, i2 ) => ( simplified( p1.conclusion ), simplified( p2.conclusion ) ) match {
          case ( TautologyClause( atom ), q4 ) => q4
          case ( q3, TautologyClause( atom ) ) => q3
          case ( q3, q4 ) =>
            q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
              q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
                Factor( Resolution( q3, i3, q4, i4 ) )._1
              } getOrElse q4
            } getOrElse q3
        }
        case Paramodulation( p1, i1, p2, i2, pos, dir ) => ( simplified( p1.conclusion ), simplified( p2.conclusion ) ) match {
          case ( q3, q4 ) =>
            q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
              q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
                Factor( Paramodulation( q3, i3, q4, i4, pos, dir ) )._1
              } getOrElse q4
            } getOrElse q3
        }
      }

      simplified( p.conclusion ) =
        simplified.get( p.conclusion ).
          orElse( simplified.get( q.conclusion ) ).
          getOrElse( q )
    }

    simplified( proof.conclusion )
  }
}
