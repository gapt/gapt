/** 
 * Description: 
**/

package at.logic.parsing.calculus.prover9

import scala.util.parsing.combinator._
import at.logic.parsing.language.prover9.Prover9TermParser
import at.logic.parsing.language.TermParser
import at.logic.syntax.language._
import at.logic.syntax.calculus._
import at.logic.parsing.calculus.SequentsParser

trait Prover9SequentsParser[+T <: SequentA] extends SequentsParser[T] with JavaTokenParsers {
  this: Prover9TermParser[TermA[TypeA]] with SequentsCreator[T] => // this means that any class mixing this trait must also mix the trait (or sub trait of) Prover9TermParser[TermA[TypeA]]
  def sequents: Parser[List[T]] = rep(sequent)
  def sequent: Parser[T] = term <~ "." ^^ {x => transformToSequent(x)} | "." ^^ {x => createSequent(Nil,Nil)}
  def transformToSequent(trm: TermA[TypeA]): T = { val r = recTransformToSequent(trm::Nil, Nil); createSequent(r._1, r._2) }
  def recTransformToSequent(l: List[TermA[TypeA]], r: List[TermA[TypeA]]): (List[TermA[TypeA]], List[TermA[TypeA]]) = (l,r) match {
    case (FunctionA(OrOp, a::b::Nil)::ls1, ls) => recTransformToSequent(a::b::ls1, ls)
    case (FunctionA(NotOp, a::Nil)::ls1, ls) => recTransformToSequent(ls1, a::ls)
    case (ls, FunctionA(OrOp, a::b::Nil)::ls1) => recTransformToSequent(ls, a::b::ls1)
    case (ls, FunctionA(NotOp, a::Nil)::ls1) => recTransformToSequent(a::ls, ls1)
    case (s1::ls1, ls2) => val r = recTransformToSequent(ls1, ls2); (s1::r._1, r._2)
    case (ls1, s2::ls2) => val r = recTransformToSequent(ls1, ls2); (r._1, s2::r._2)
    case (Nil, Nil) => (Nil, Nil)
    case x => throw new ParsingException("Error while transforming term: " + x + " into a sequent")
  }
}
