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
import at.logic.language.hol._
import at.logic.language.lambda._
import at.logic.language.lambda.types.{FunctionType, To, Ti}

trait SimpleHOLParser extends HOLParser with JavaTokenParsers with at.logic.language.lambda.types.Parsers {
  def goal = term

  def term: Parser[HOLExpression] = (non_formula | formula)
  def formula: Parser[HOLFormula] = (neg | atom | and | or | imp | forall | exists | variable | constant) ^? {
    case trm: Formula => trm.asInstanceOf[HOLFormula]
  }
  def non_formula: Parser[HOLExpression] = (abs | variable | constant | var_func | const_func)
  def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => HOLVar(x, tp) }
  def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => HOLConst(x, tp) }
  def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
  def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
  def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
  def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => HOLAbs(v,x)}
  def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
  def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
  def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
  def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
  def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => Atom(HOLVar(x, FunctionType(To, params.map(_.exptype))), params)
  }
  def const_atom: Parser[HOLFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => Atom(HOLConst(x, FunctionType(To, params.map(_.exptype))), params)
  }
  def equality: Parser[HOLFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
  //def eq_infix: Parser[HOLFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
  def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
  def var_func: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {
    case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(HOLVar(x, FunctionType(tp, (params.map(_.exptype)))), params)
  }

  def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ~ ":" ~ Type ^^ {
    case x ~ "(" ~ params ~ ")" ~ ":" ~ tp  => Function(HOLConst(x, FunctionType(tp, (params.map(_.exptype)))) , params)
  }

  protected def symbol: Parser[String] = symbols.r
  def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';
    protected val word: String = """[a-zA-Z0-9$_{}]*"""

}

