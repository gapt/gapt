/*
 * FOLMatchingAlgorithm.scala
 *
 */
package at.logic.gapt.expr.fol

import at.logic.gapt.expr._

object FOLMatchingAlgorithm {
  /**
   * Computes a FOLSubstitution that turns term from into term to, if one exists.
   *
   * @param from A LambdaExpression.
   * @param to A LambdaExpression.
   * @param forbiddenVars A set of variables that cannot be in the domain of the FOLSubstitution. Defaults to the empty set.
   * @return If there is a variable FOLSubstitution that turns from into to And doesn't contain any elements of forbiddenVars, it is returned. Otherwise None.
   */
  def matchTerms( from: FOLExpression, to: FOLExpression, forbiddenVars: Set[FOLVar] = Set() ): Option[FOLSubstitution] = computeSubstitution( List( ( from, to ) ), forbiddenVars )

  /**
   * Recursively looks for a FOLSubstitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of FOLExpressions.
   * @param forbiddenVars A set of variables that cannot be in the domain of the FOLSubstitution.
   * @return
   */
  private def computeSubstitution( pairs: List[( FOLExpression, FOLExpression )], forbiddenVars: Set[FOLVar] ): Option[FOLSubstitution] = pairs match {
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

        case ( And( a, b ), And( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Or( a, b ), Or( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Imp( a, b ), Imp( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Neg( a ), Neg( b ) ) =>
          computeSubstitution( ( a, b ) :: rest, forbiddenVars )

        case ( Ex( v1, f1 ), Ex( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, forbiddenVars + v1 + v2 )

        case ( All( v1, f1 ), All( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, forbiddenVars + v1 + v2 )

        case ( v: FOLVar, exp: FOLTerm ) =>
          if ( forbiddenVars contains v )
            None
          else {
            val sub = FOLSubstitution( v, exp )
            val restNew = rest map ( ( p: ( FOLExpression, FOLExpression ) ) => ( sub( p._1 ), p._2 ) )
            val subRest = computeSubstitution( restNew, forbiddenVars + v )

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
