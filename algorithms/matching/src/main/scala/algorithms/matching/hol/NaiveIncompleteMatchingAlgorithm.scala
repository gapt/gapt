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
import at.logic.language.hol._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._

object NaiveIncompleteMatchingAlgorithm extends MatchingAlgorithm[HOLExpression] {

  def matchTerm(term: HOLExpression, posInstance: HOLExpression): Option[Substitution[HOLExpression]] =
    matchTerm(term, posInstance, posInstance.getFreeAndBoundVariables._1.toList)

  // restrictedDomain: variables to be treated as constants.
  def matchTerm(term: HOLExpression, posInstance: HOLExpression, restrictedDomain: List[Var]): Option[Substitution[HOLExpression]] = 
    {
      val res = holMatch(term, posInstance)(restrictedDomain)
      res match {
        case None => println(term.toStringSimple + " did not match " + posInstance.toStringSimple)
        case Some(_) => println(term.toStringSimple + " matches " + posInstance.toStringSimple)

      }
      res 
    }

  def holMatch( s: HOLExpression, t: HOLExpression )(implicit restrictedDomain: List[Var]) : Option[Substitution[HOLExpression]] =
    (s, t) match {
      case ( HOLApp(s_1, s_2), HOLApp(t_1, t_2) ) => merge( holMatch(s_1, t_1), holMatch(s_2, t_2) )
      case ( s : HOLVar, _ ) if !restrictedDomain.contains(s) => Some(Substitution[HOLExpression]( s, t  ) )
      case ( v1 : HOLVar, v2 : HOLVar ) if v1 == v2 => Some(Substitution[HOLExpression]())
      case ( v1 : HOLVar, v2 : HOLVar ) if v1 != v2 =>  None
      case ( c1 : HOLConst, c2 : HOLConst ) if c1 == c2 => Some(Substitution[HOLExpression]())
      case ( HOLAbsInScope(v1, e1), HOLAbsInScope(v2, e2) ) if v1 == v2 => holMatch( e1, e2 )
      case ( HOLAbsInScope(v1, e1), HOLAbsInScope(v2, e2) ) if v1 != v2 => None
      case _ => None
    }

  def merge( s1: Option[Substitution[HOLExpression]], s2: Option[Substitution[HOLExpression]] ) : Option[Substitution[HOLExpression]] = (s1, s2) match {
    case (Some(ss1), Some(ss2)) => {
      if (!ss1.map.forall( s1 =>
        ss2.map.forall( s2 =>
          s1._1 != s2._1 || s1._2 == s2._2 ) ) )
        None
      else
      {
        val new_list = ss2.map.filter( s2 => ss1.map.forall( s1 => s1._1 != s2._1 ) )
        Some(ss1 ::: Substitution[HOLExpression]( new_list ) )
      }
    }
    case (None, _) => None
    case (_, None) => None
  }
}
