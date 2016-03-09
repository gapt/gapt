package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.{ freeVariables, HOLAtom }
import at.logic.gapt.proofs.HOLClause

import scala.collection.mutable

object simplifyResolutionProof {
  def apply( proof: ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()

    def simplified( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case _: InitialClause => Factor( p )._1
      case Instance( p1, subst1 ) => simplified( p1 ) match {
        case q1 if freeVariables( q1.conclusion ) intersect subst1.domain isEmpty => q1
        case Instance( q2, subst2 ) => Factor( Instance( q2, subst1 compose subst2 ) )._1
        case TautologyClause( atom ) => TautologyClause( subst1( atom ).asInstanceOf[HOLAtom] )
        case ReflexivityClause( term ) => ReflexivityClause( subst1( term ) )
        case q1 => Factor( Instance( q1, subst1 ) )._1
      }
      case Factor( p1, i1, j1 ) => simplified( p1 )
      case Resolution( p1, i1, p2, i2 ) => ( simplified( p1 ), simplified( p2 ) ) match {
        case ( TautologyClause( atom ), q4 ) => q4
        case ( q3, TautologyClause( atom ) ) => q3
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Resolution( q3, i3, q4, i4 ) )._1
            } getOrElse q4
          } getOrElse q3
      }
      case Paramodulation( p1, i1, p2, i2, pos, dir ) => ( simplified( p1 ), simplified( p2 ) ) match {
        case ( q3, q4 ) =>
          q3.conclusion.indicesWhere( _ == p1.conclusion( i1 ) ).find( _ sameSideAs i1 ) map { i3 =>
            q4.conclusion.indicesWhere( _ == p2.conclusion( i2 ) ).find( _ sameSideAs i2 ) map { i4 =>
              Factor( Paramodulation( q3, i3, q4, i4, pos, dir ) )._1
            } getOrElse q4
          } getOrElse q3
      }
      case p @ Splitting( splittingClause, part1, part2, case1, case2 ) =>
        Splitting( simplified( splittingClause ), part1, part2, simplified( case1 ), simplified( case2 ) )
    } ) ensuring { res => res.conclusion == res.conclusion.distinct && res.conclusion.isSubMultisetOf( p.conclusion ) }

    simplified( proof )
  }
}
