package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.FOLClause

import scala.collection.mutable

object simplifyResolutionProof {
  def apply( proof: ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()

    def simp( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case _: InitialClause => p
      case Instance( p1, subst1 ) => simp( p1 ) match {
        case q @ Instance( q2, subst2 ) =>
          val q_ = Factor( Instance( q2, subst1 compose subst2 ) )._1
          // ignore instances that substitute back and forth
          if ( q_.conclusion == q2.conclusion ) q2 else q_
        case TautologyClause( atom )   => TautologyClause( subst1( atom ) )
        case ReflexivityClause( term ) => ReflexivityClause( subst1( term ) )
        case q =>
          val q_ = Factor( Instance( q, subst1 ) )._1
          // ignore instances that do not change anything
          if ( q_.conclusion == q.conclusion ) q else q_
      }
      case Factor( p1, i1, j1 ) => simp( p1 )
      case Resolution( p1, i1, p2, i2 ) => ( simp( p1 ), simp( p2 ) ) match {
        case ( TautologyClause( atom ), q4 ) => q4
        case ( q3, TautologyClause( atom ) ) => q3
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Resolution( q3, i3, q4, i4 ) )._1
            } getOrElse q4
          } getOrElse q3
      }
      case Paramodulation( p1, i1, p2, i2, pos, dir ) => ( simp( p1 ), simp( p2 ) ) match {
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Paramodulation( q3, i3, q4, i4, pos, dir ) )._1
            } getOrElse q4
          } getOrElse q3
      }
    } )

    val cycleFreeProof = mutable.Map[FOLClause, ResolutionProof]()
    simp( proof ) dagLikeForeach { p =>
      cycleFreeProof.getOrElseUpdate( p.conclusion, p match {
        case _: InitialClause             => p
        case Instance( p1, subst )        => Instance( cycleFreeProof( p1.conclusion ), subst )
        case Factor( p1, i, j )           => Factor( cycleFreeProof( p1.conclusion ), i, j )
        case Resolution( p1, i1, p2, i2 ) => Resolution( cycleFreeProof( p1.conclusion ), i1, cycleFreeProof( p2.conclusion ), i2 )
        case Paramodulation( p1, i1, p2, i2, pos, dir ) =>
          Paramodulation( cycleFreeProof( p1.conclusion ), i1, cycleFreeProof( p2.conclusion ), i2, pos, dir )
      } )
    }

    cycleFreeProof( simp( proof ).conclusion )
  }
}
