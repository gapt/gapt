/*
 * FOLMatchingAlgorithm.scala
 *
 */
package at.logic.algorithms.matching

import at.logic.language.fol._
import at.logic.language.hol.HOLExpression

object FOLMatchingAlgorithm {

  /**
   * Computes a substitution that turns term from into term to, if one exists.
   *
   * @param from A HOLExpression.
   * @param to A HOLExpression.
   * @param forbiddenVars A list of variables that cannot be in the domain of the substitution. Defaults to Nil.
   * @return If there is a variable substitution that turns from into to and doesn't contain any elements of forbiddenVars, it is returned. Otherwise None.
   */
  def matchTerms( from: FOLExpression, to: FOLExpression, forbiddenVars: List[FOLVar] = Nil ): Option[Substitution] = computeSubstitution( List( ( from, to ) ), forbiddenVars )

  /**
   * Recursively looks for a substitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of HOLExpressions.
   * @param forbiddenVars A list of variables that cannot be in the domain of the substitution.
   * @return
   */
  def computeSubstitution( pairs: List[( HOLExpression, HOLExpression )], forbiddenVars: List[FOLVar] ): Option[Substitution] = pairs match {
    case Nil => Some( Substitution() )
    case first :: rest =>
      first match {
        case ( a1, a2 ) if a1 == a2 => computeSubstitution( rest, forbiddenVars )

        case ( FOLConst( c1 ), FOLConst( c2 ) ) =>
          if ( c1 == c2 )
            computeSubstitution( rest, forbiddenVars )
          else
            None

        case ( Function( f1, args1 ), Function( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, forbiddenVars )

        case ( Atom( f1, args1 ), Atom( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, forbiddenVars )

        case ( And( a, b ), And( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Or( a, b ), Or( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Imp( a, b ), Imp( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, forbiddenVars )

        case ( Neg( a ), Neg( b ) ) =>
          computeSubstitution( ( a, b ) :: rest, forbiddenVars )

        case ( ExVar( v1, f1 ), ExVar( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, v1 :: v2 :: forbiddenVars )

        case ( AllVar( v1, f1 ), AllVar( v2, f2 ) ) =>
          computeSubstitution( ( f1, f2 ) :: rest, v1 :: v2 :: forbiddenVars )

        case ( v: FOLVar, exp: FOLExpression ) =>
          if ( forbiddenVars contains v )
            None
          else {
            val sub = Substitution( v, exp )
            val restNew = rest map ( ( p: ( HOLExpression, HOLExpression ) ) => ( sub( p._1 ), sub( p._2 ) ) )
            val subRest = computeSubstitution( restNew, v :: forbiddenVars )

            subRest match {
              case None => None
              case Some( s ) =>
                if ( !s.folmap.contains( v ) )
                  Some( Substitution( s.folmap + ( v -> exp ) ) )
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
