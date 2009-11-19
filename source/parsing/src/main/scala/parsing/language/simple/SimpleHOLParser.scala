/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.simple

import scala.util.parsing.combinator._
import scala.util.matching.Regex
import at.logic.parsing.language.HOLParser
import at.logic.language.hol.HigherOrderLogic._
import at.logic.language.lambda.Types.TA
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.lambda.Symbols.VariableStringSymbol
import at.logic.language.hol.LogicSymbols.ConstantStringSymbol

trait SimpleHOLParser extends HOLParser with JavaTokenParsers with at.logic.language.lambda.Types.Parsers {
  def term: Parser[HOLTerm] = (formula | non_formula)
  def formula: Parser[HOLFormula] = (atom | and | or | imp | neg | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}
  def non_formula: Parser[HOLTerm] = (variable | constant)
  def variable: Parser[HOLTerm] = regex(new Regex("[u-z]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => Var(new VariableStringSymbol(x), tp, hol)}
  def constant: Parser[HOLTerm] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => Var(new ConstantStringSymbol(x), tp, hol)}
  def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
  def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
  def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
  def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
  def atom: Parser[HOLFormula] = (var_atom | const_atom)
  def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new VariableStringSymbol(x), params)}
  def const_atom: Parser[HOLFormula] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params)}
  private def word: String = """[a-zA-Z0-9$_]*"""
  private def symbol: Parser[String] = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073]+""".r // +-*/\^<>=`~?@&|!#';
}

