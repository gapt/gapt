/*
 * naiveIncompleteMatchingAlgorithm.scala
 *
 */

package at.logic.gapt.language.hol.algorithms

import at.logic.gapt.expr._
import at.logic.gapt.language.hol.HOLSubstitution

object NaiveIncompleteMatchingAlgorithm {

  def matchTerm( term: LambdaExpression, posInstance: LambdaExpression ): Option[HOLSubstitution] =
    matchTerm( term, posInstance, freeVariables( posInstance ) )

  // restrictedDomain: variables to be treated as constants.
  def matchTerm( term: LambdaExpression, posInstance: LambdaExpression, restrictedDomain: List[Var] ): Option[HOLSubstitution] =
    holMatch( term, posInstance )( restrictedDomain )

  def holMatch( s: LambdaExpression, t: LambdaExpression )( implicit restrictedDomain: List[Var] ): Option[HOLSubstitution] =
    ( s, t ) match {
      case ( App( s_1, s_2 ), App( t_1, t_2 ) ) => merge( holMatch( s_1, t_1 ), holMatch( s_2, t_2 ) )
      case ( s: Var, t: LambdaExpression ) if !restrictedDomain.contains( s ) && s.exptype == t.exptype => Some( HOLSubstitution( s, t ) )
      case ( v1: Var, v2: Var ) if v1 == v2 => Some( HOLSubstitution() )
      case ( v1: Var, v2: Var ) if v1 != v2 => None
      case ( c1: Const, c2: Const ) if c1 == c2 => Some( HOLSubstitution() )
      case ( Abs( v1, e1 ), Abs( v2, e2 ) ) => holMatch( e1, e2 ) //TODO: add sub v2 <- v1 on e2 and check
      case _ => None
    }

  def merge( s1: Option[HOLSubstitution], s2: Option[HOLSubstitution] ): Option[HOLSubstitution] = ( s1, s2 ) match {
    case ( Some( ss1 ), Some( ss2 ) ) => {
      if ( !ss1.map.forall( s1 =>
        ss2.map.forall( s2 =>
          s1._1 != s2._1 || s1._2 == s2._2 ) ) )
        None
      else {
        val new_list = ss2.holmap.filter( s2 => ss1.map.forall( s1 => s1._1 != s2._1 ) )
        Some( HOLSubstitution( ss1.holmap ++ new_list ) )
      }
    }
    case ( None, _ ) => None
    case ( _, None ) => None
  }
}
