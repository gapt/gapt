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
  def matchTerms( from: FOLExpression, to: FOLExpression, forbiddenVars: Set[FOLVar] = Set() ): Option[FOLSubstitution] =
    computeSubstitution( List( from -> to ), forbiddenVars map { v => v -> v } toMap )

  /**
   * Recursively looks for a FOLSubstitution σ such that for each (a, b) ∈ pairs, σ(a) = b.
   *
   * @param pairs A list of pairs of FOLExpressions.
   * @param alreadyFixedSubst The partial substition which is already fixed, and can no longer be changed.
   * @return
   */
  private def computeSubstitution( pairs: List[( FOLExpression, FOLExpression )], alreadyFixedSubst: Map[FOLVar, FOLTerm] ): Option[FOLSubstitution] = pairs match {
    case Nil => Some( FOLSubstitution( alreadyFixedSubst ) )
    case first :: rest =>
      first match {
        case ( FOLFunction( f1, args1 ), FOLFunction( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, alreadyFixedSubst )

        case ( FOLAtom( f1, args1 ), FOLAtom( f2, args2 ) ) if f1 == f2 && args1.length == args2.length =>
          computeSubstitution( ( args1 zip args2 ) ++ rest, alreadyFixedSubst )

        case ( Top(), Top() )       => computeSubstitution( rest, alreadyFixedSubst )
        case ( Bottom(), Bottom() ) => computeSubstitution( rest, alreadyFixedSubst )

        case ( And( a, b ), And( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, alreadyFixedSubst )

        case ( Or( a, b ), Or( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, alreadyFixedSubst )

        case ( Imp( a, b ), Imp( c, d ) ) =>
          computeSubstitution( ( a, c ) :: ( b, d ) :: rest, alreadyFixedSubst )

        case ( Neg( a ), Neg( b ) ) =>
          computeSubstitution( ( a, b ) :: rest, alreadyFixedSubst )

        case ( v: FOLVar, exp ) if alreadyFixedSubst.get( v ).contains( exp ) =>
          computeSubstitution( rest, alreadyFixedSubst )

        case ( v: FOLVar, exp: FOLTerm ) if !alreadyFixedSubst.contains( v ) =>
          val sub = FOLSubstitution( v, exp )
          val restNew = rest map { case ( f, t ) => sub( f ) -> t }
          computeSubstitution( restNew, alreadyFixedSubst + ( v -> exp ) )

        case _ => None
      }
  }
}
