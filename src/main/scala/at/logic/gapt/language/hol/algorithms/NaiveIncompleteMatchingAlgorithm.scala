/*
 * naiveIncompleteMatchingAlgorithm.scala
 *
 */

package at.logic.gapt.language.hol.algorithms

import at.logic.gapt.language.hol._

object NaiveIncompleteMatchingAlgorithm {

  def matchTerm( term: HOLExpression, posInstance: HOLExpression ): Option[HOLSubstitution] =
    matchTerm( term, posInstance, freeVariables( posInstance ) )

  // restrictedDomain: variables to be treated as constants.
  def matchTerm( term: HOLExpression, posInstance: HOLExpression, restrictedDomain: List[HOLVar] ): Option[HOLSubstitution] =
    holMatch( term, posInstance )( restrictedDomain )

  def holMatch( s: HOLExpression, t: HOLExpression )( implicit restrictedDomain: List[HOLVar] ): Option[HOLSubstitution] =
    ( s, t ) match {
      case ( HOLApp( s_1, s_2 ), HOLApp( t_1, t_2 ) ) => merge( holMatch( s_1, t_1 ), holMatch( s_2, t_2 ) )
      case ( s: HOLVar, t: HOLExpression ) if !restrictedDomain.contains( s ) && s.exptype == t.exptype => Some( HOLSubstitution( s, t ) )
      case ( v1: HOLVar, v2: HOLVar ) if v1 == v2 => Some( HOLSubstitution() )
      case ( v1: HOLVar, v2: HOLVar ) if v1 != v2 => None
      case ( c1: HOLConst, c2: HOLConst ) if c1 == c2 => Some( HOLSubstitution() )
      case ( HOLAbs( v1, e1 ), HOLAbs( v2, e2 ) ) => holMatch( e1, e2 ) //TODO: add sub v2 <- v1 on e2 and check
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
