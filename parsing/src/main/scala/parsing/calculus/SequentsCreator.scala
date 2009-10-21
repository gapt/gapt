/** 
 * Description: 
**/

package at.logic.parsing.calculus

import at.logic.syntax.calculus._
import at.logic.syntax.language._
import at.logic.syntax.calculus.resolution._

trait SequentsCreator[+T <: SequentA] {
  def createSequent(l: List[TermA[TypeA]], r: List[TermA[TypeA]]): T
}

trait ClausesCreator extends SequentsCreator[Clause] {
  def createSequent(l: List[TermA[TypeA]], r: List[TermA[TypeA]]): Clause = Clause(l.map(x => ClauseTermOccurrence(x)), r.map(x => ClauseTermOccurrence(x)))
}

