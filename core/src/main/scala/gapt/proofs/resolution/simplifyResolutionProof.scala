package gapt.proofs.resolution

import gapt.expr.freeVariables

import scala.collection.mutable

object simplifyResolutionProof {
  def apply( proof: ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()

    def simplified( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case _: InitialClause => Factor( p )
      case Subst( p1, subst1 ) => simplified( p1 ) match {
        case q1 if freeVariables( q1.conclusion ) intersect subst1.domain isEmpty => q1
        case Subst( q2, subst2 ) => Factor( Subst( q2, subst1 compose subst2 ) )
        case Taut( atom ) => Taut( subst1( atom ) )
        case Refl( term ) => Refl( subst1( term ) )
        case q1 => Factor( Subst( q1, subst1 ) )
      }
      case Factor( p1, i1, j1 ) => simplified( p1 )
      case Resolution( p1, i1, p2, i2 ) => ( simplified( p1 ), simplified( p2 ) ) match {
        case ( Taut( atom ), q4 ) => q4
        case ( q3, Taut( atom ) ) => q3
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Resolution( q3, i3, q4, i4 ) )
            } getOrElse q4
          } getOrElse q3
      }
      case Paramod( p1, i1, dir, p2, i2, pos ) => ( simplified( p1 ), simplified( p2 ) ) match {
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Paramod( q3, i3, dir, q4, i4, pos ) )
            } getOrElse q4
          } getOrElse q3
      }
      case Flip( p1, i1 ) => simplified( p1 ) match {
        case q2 =>
          q2.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i2 =>
            Factor( Flip( q2, i2 ) )
          } getOrElse q2
      }
      // FIXME: descend into propositional part?
      case _ => Factor( p )
    } ) ensuring { res => res.conclusion == res.conclusion.distinct && res.conclusion.isSubMultisetOf( p.conclusion ) }

    simplified( proof )
  }
}
