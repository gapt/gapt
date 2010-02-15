/*
 * naiveIncompleteMatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching.hol

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import scala.collection.immutable.EmptySet

object NaiveIncompleteMatchingAlgorithm extends MatchingAlgorithm {
  def matchTerm(term: LambdaExpression, posInstance: LambdaExpression): Option[Substitution] = holMatch(term.asInstanceOf[HOLTerm], ground(posInstance).asInstanceOf[HOLTerm])

  def holMatch( s: HOLTerm, t: HOLTerm ) : Option[Substitution] =
    (s, t) match {
      case ( HOLApp(s_1, s_2), HOLApp(t_1, t_2) ) => merge( holMatch(s_1, t_1), holMatch(s_2, t_2) )
      // FIXME: we should be able to get a HOLVar object from the case, so that casting is not necessary...
      case ( HOLVar(_), _ ) if !getVars(t).contains(s.asInstanceOf[HOLVar]) => Some(Substitution( s.asInstanceOf[HOLVar], t  ) )
      case ( v1 @ HOLVar(_), v2 @ HOLVar(_) ) if v1 == v2 => Some(Substitution())
      case ( v1 @ HOLVar(_), v2 @ HOLVar(_) ) if v1 != v2 =>  {
        None
      }
      case ( c1 @ HOLConst(_), c2 @ HOLConst(_) ) if c1 == c2 => Some(Substitution())
      case ( HOLAbsInScope(v1, e1), HOLAbsInScope(v2, e2) ) if v1 == v2 => holMatch( e1, e2 )
      case ( HOLAbsInScope(v1, e1), HOLAbsInScope(v2, e2) ) if v1 != v2 => None
      case _ => None
    }

  def merge( s1: Option[Substitution], s2: Option[Substitution] ) : Option[Substitution] = (s1, s2) match {
    case (Some(ss1), Some(ss2)) => {
      if (!ss1.map.forall( s1 =>
        ss2.map.forall( s2 =>
          s1._1 != s2._1 || s1._2 == s2._2 ) ) )
        None
      else
      {
        val new_list = ss2.map.filter( s2 => ss1.map.forall( s1 => s1._1 != s2._1 ) )
        Some(ss1 ::: Substitution( new_list ) )
      }
    }
    case (None, _) => None
    case (_, None) => None
  }

  def getVars( t: HOLTerm ) : Set[HOLVar] = t match {
    case HOLApp(t_1, t_2) => getVars( t_1 ) ++ getVars( t_2 )
    // FIXME: we should be able to get a HOLVar object from the case, so that casting is not necessary...
    case HOLVar(_) => (new EmptySet()) + t.asInstanceOf[HOLVar]
    case HOLAbs(_, sub) => getVars( sub )
    case _ => new EmptySet()
  }
}