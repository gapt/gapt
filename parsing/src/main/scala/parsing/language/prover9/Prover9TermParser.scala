/**
 * Description: Implementation of term parser using prover9 BNF
 */

package at.logic.parsing.language.prover9

import scala.util.parsing.combinator._
import scala.util.matching.Regex
import at.logic.parsing.language.TermParser
import at.logic.syntax.language._

trait Prover9TermParser[+T <: TermA[TypeA]] extends TermParser[T] with JavaTokenParsers {
  def term: Parser[T] = (function | variable | constant | infix_bin_function)
  def variable: Parser[T] = regex(new Regex("[u-z]" + word)) ^^ {x => createVariable(x)}
  def constant: Parser[T] = regex(new Regex("[a-tA-Z0-9]" + word)) ^^ {x => createConstant(x)}
  def function: Parser[T] = {symbol | regex(new Regex("""[a-zA-Z0-9$_]""" + word))} ~ {"(" ~> repsep(term,",")} <~ ")" ^^ {case name ~ params => createFunction(name, params)}
  def infix_bin_function: Parser[T] = "(" ~> {term <~ ")"} ~ symbol ~ {"(" ~> term} <~ ")" ^^ {case t1 ~ name ~ t2 => createFunction(name, t1::t2::Nil)}
  private def word: String = """[a-zA-Z0-9$_]*"""
  private def symbol: Parser[String] = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073]+""".r // +-*/\^<>=`~?@&|!#';
  protected def createVariable(name: String): T
  protected def createConstant(name: String): T
  protected def createFunction(sym: String, params: List[TermA[TypeA]]): T
}
