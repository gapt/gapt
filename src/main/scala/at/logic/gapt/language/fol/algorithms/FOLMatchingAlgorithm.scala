/*
 * FOLMatchingAlgorithm.scala
 *
 */
package at.logic.gapt.language.fol.algorithms

import at.logic.gapt.language.fol._

object FOLMatchingAlgorithm {

  /**
   * Computes a FOLSubstitution that turns term from into term to, if one exists.
   *
   * @param from A HOLExpression.
   * @param to A HOLExpression.
   * @param forbiddenVars A list of variables that cannot be in the domain of the FOLSubstitution. Defaults to Nil.
   * @return If there is a variable FOLSubstitution that turns from into to FOLAnd doesn't contain any elements of forbiddenVars, it is returned. Otherwise None.
   */
  def matchTerms( from: FOLExpression, to: FOLExpression, forbiddenVars: List[FOLVar] = Nil ): Option[FOLSubstitution] = computeSubstitution( List( ( from, to ) ), forbiddenVars )

  /**
   * Recursively looks for a FOLSubstitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of FOLExpressions.
   * @param forbiddenVars A list of variables that cannot be in the domain of the FOLSubstitution.
   * @return
   */
  private def computeSubstitution( pairs: List[( FOLExpression, FOLExpression )], forbiddenVars: List[FOLVar] ): Option[FOLSubstitution] = pairs match {
    case Nil => Some( FOLSubstitution() )
    case first :: rest =>
      first match {
        case ( a1, a2 ) if a1 == a2 => computeSubstitution( rest, forbiddenVars )

        case ( FOLConst( c1 ), FOLConst( c2 ) ) =>
          if ( c1 == c2 )
            computeSubstitution( rest, forbiddenVars )
          else
            None

        case ( FOLFunction( f1, args1 ), FOLFunction( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, forbiddenVars )

        case ( FOLAtom( f1, args1 ), FOLAtom( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, forbiddenVars )

        case ( FOLAnd( a, b ), FOLAnd( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( FOLOr( a, b ), FOLOr( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( FOLImp( a, b ), FOLImp( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( FOLNeg( a ), FOLNeg( b ) ) =>
          computeSubstitution( ( a, b ) :: rest, forbiddenVars )

        case ( FOLExVar( v1, f1 ), FOLExVar( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, v1 :: v2 :: forbiddenVars )

        case ( FOLAllVar( v1, f1 ), FOLAllVar( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, v1 :: v2 :: forbiddenVars )

        case ( v: FOLVar, exp: FOLExpression ) =>
          if ( forbiddenVars contains v )
            None
          else {
            val sub = FOLSubstitution( v, exp )
            val restNew = rest map ( ( p: ( FOLExpression, FOLExpression ) ) => ( sub( p._1 ), p._2 ) )
            val subRest = computeSubstitution( restNew, v :: forbiddenVars )

            subRest match {
              case None => None
              case Some( s ) =>
                if ( !s.folmap.contains( v ) )
                  Some( FOLSubstitution( s.folmap + ( v -> exp ) ) )
                else if ( s( v ) == exp )
                  subRest
                else
                  None
            }
          }

        case _ => None
      }
  }
}
