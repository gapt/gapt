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
import at.logic.language.hol.propositions.{HOLVar,HOLConst}
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.fol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

trait SimpleFOLParser extends SimpleHOLParser {
  override def term: Parser[HOLTerm] = (formula | non_formula)
  override def formula: Parser[HOLFormula] = (const_atom | and | or | imp | neg | forall | exists) ^? {case trm: FOLFormula => trm.asInstanceOf[FOLFormula]}
  override def non_formula: Parser[HOLTerm] = (variable | constant | const_func) ^? {case trm: FOLTerm => trm.asInstanceOf[FOLTerm]}

  override def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ^^ {case x => FOLFactory.createVar(new VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}
  override def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word)) ^^ {case x => FOLFactory.createVar(new ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}

  override def const_atom: Parser[HOLFormula] = regex(new Regex("[A-Z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  override def const_func: Parser[HOLTerm] = regex(new Regex("[a-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
}

