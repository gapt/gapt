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
import at.logic.language.hol.{HOLVar,HOLConst, HOLExpression, HOLFormula}
import at.logic.language.fol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol

trait SimpleFOLParser extends SimpleHOLParser {
  override def term: Parser[HOLExpression] = (formula | non_formula)
  override def formula: Parser[HOLFormula] = (and | or | imp | neg | forall | exists | const_atom) ^? {case trm: FOLFormula => trm.asInstanceOf[FOLFormula]}
  override def non_formula: Parser[HOLExpression] = (const_func | variable | constant) ^? {case trm: FOLTerm => trm.asInstanceOf[FOLTerm]}

  override def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ^^ {case x => FOLFactory.createVar(new VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}
  override def constant: Parser[HOLConst] = regex(new Regex("[a-t]" + word)) ^^ {case x => FOLFactory.createVar(new ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}

  override def const_atom: Parser[HOLFormula] = const_atom1 | const_atom2
  def const_atom1: Parser[HOLFormula] = regex(new Regex("["+symbols+"A-Z]" + word)) ~ "(" ~ repsep(non_formula,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  def const_atom2: Parser[HOLFormula] = regex(new Regex("["+symbols+"A-Z]" + word)) ^^ {case x => Atom(new ConstantStringSymbol(x), Nil)}
  override def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-z]" + word)) ~ "(" ~ repsep(non_formula,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(new ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}

  override def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x.asInstanceOf[FOLFormula],y.asInstanceOf[FOLFormula])}
  override def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x.asInstanceOf[FOLFormula],y.asInstanceOf[FOLFormula])}
  override def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x.asInstanceOf[FOLFormula],y.asInstanceOf[FOLFormula])}
  override def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x.asInstanceOf[FOLFormula])}
  override def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
  override def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v.asInstanceOf[FOLVar],x.asInstanceOf[FOLFormula])}
  override def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v.asInstanceOf[FOLVar],x.asInstanceOf[FOLFormula])}
}

