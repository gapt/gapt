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
import scala.collection.immutable.EmptySet
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._

// should use the restricted domain instead of grounding the second term
object NaiveIncompleteMatchingAlgorithm extends MatchingAlgorithm[HOLExpression] {
  def matchTerm(term: HOLExpression, posInstance: HOLExpression, restrictedDomain: List[Var]): Option[Substitution[HOLExpression]] = holMatch(term.asInstanceOf[HOLExpression], ground(posInstance).asInstanceOf[HOLExpression])

   // in all instances of the algorithm we ground the second term by replacing all free variables by constants
  private def ground(e: LambdaExpression): LambdaExpression = e match {
    case v @ Var(VariableStringSymbol(s),ta) if v.asInstanceOf[Var].isFree => v.factory.createVar(ConstantStringSymbol(s), ta)
    case v: Var => v
    case App(a,b) => App(ground(a), ground(b))
    case abs: Abs => Abs(abs.variable, ground(abs.expressionInScope))
  }
  
  def holMatch( s: HOLExpression, t: HOLExpression ) : Option[Substitution[HOLExpression]] =
    (s, t) match {
      case ( HOLApp(s_1, s_2), HOLApp(t_1, t_2) ) => merge( holMatch(s_1, t_1), holMatch(s_2, t_2) )
      // FIXME: we should be able to get a HOLVar object from the case, so that casting is not necessary...
      case ( HOLVar(_, _), _ ) if !getVars(t).contains(s.asInstanceOf[HOLVar]) => Some(Substitution[LambdaExpression]( s.asInstanceOf[HOLVar], t  ) )
      case ( v1 @ HOLVar(_,_), v2 @ HOLVar(_,_) ) if v1 == v2 => Some(Substitution[LambdaExpression]())
      case ( v1 @ HOLVar(_,_), v2 @ HOLVar(_,_) ) if v1 != v2 =>  {
        None
      }
      case ( c1 @ HOLConst(_,_), c2 @ HOLConst(_,_) ) if c1 == c2 => Some(Substitution[LambdaExpression]())
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
        Some(ss1 ::: Substitution[LambdaExpression]( new_list ) )
      }
    }
    case (None, _) => None
    case (_, None) => None
  }

  def getVars( t: HOLExpression ) : Set[HOLVar] = t match {
    case HOLApp(t_1, t_2) => getVars( t_1 ) ++ getVars( t_2 )
    // FIXME: we should be able to get a HOLVar object from the case, so that casting is not necessary...
    case HOLVar(_,_) => (new EmptySet()) + t.asInstanceOf[HOLVar]
    case HOLAbs(_, sub) => getVars( sub )
    case _ => new EmptySet()
  }
}
