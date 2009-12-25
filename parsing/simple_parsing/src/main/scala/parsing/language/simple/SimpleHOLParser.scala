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
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.lambda.types.TA
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

trait SimpleHOLParser extends HOLParser with JavaTokenParsers with at.logic.language.lambda.types.Parsers {
  def term: Parser[HOLTerm] = (formula | non_formula)
  def formula: Parser[HOLFormula] = (atom | and | or | imp | neg | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}
  def non_formula: Parser[HOLTerm] = (variable | constant | var_func | const_func)
  def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new VariableStringSymbol(x), tp).asInstanceOf[HOLVar]}
  def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new ConstantStringSymbol(x), tp).asInstanceOf[HOLConst]}
  def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
  def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
  def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
  def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
  def atom: Parser[HOLFormula] = (var_atom | const_atom)
  def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
  def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
  def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new VariableStringSymbol(x), params)}
  def const_atom: Parser[HOLFormula] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params)}
  def var_func: Parser[HOLTerm] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
  def const_func: Parser[HOLTerm] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp  => Function(new ConstantStringSymbol(x), params, tp)}
  protected def word: String = """[a-zA-Z0-9$_]*"""
  protected def symbol: Parser[String] = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073]+""".r // +-*/\^<>=`~?@&|!#';
}

