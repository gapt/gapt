/*
 * SimpleResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi.simple

import scala.util.parsing.combinator._
import scala.util.matching.Regex
import at.logic.parsing.calculi.ResolutionParser
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.robinson._

/*
 * In order to allow a complex inheritence structure where the resolutionParser trait is mixed
 * with HOL or FOL parsers and must override a method there on the same time we have created these
 * two helper classes.
 */
trait SimpleResolutionParserHOL extends SimpleResolutionParser[Clause] with SimpleHOLParser {
  override def formula = formula2
  override def neg = neg2
  def clause: Parser[Clause] = repsep(formula,"|") ~ "." ^^ {case ls ~ "." => new Clause(ls.filter(filterPosFormulas).map(stripNeg),ls.filter(x => !filterPosFormulas(x)))}
}
trait SimpleResolutionParserFOL extends SimpleResolutionParser[Clause] with SimpleFOLParser {
  override def formula = formula2
  override def neg = neg2
  def clause: Parser[Clause] = repsep(formula,"|") ~ "." ^^ {case ls ~ "." => new Clause(ls.filter(filterPosFormulas).map(stripNeg),ls.filter(x => !filterPosFormulas(x)))}
}

trait SimpleResolutionParser[V <: Sequent] extends ResolutionParser[V] {
  // used instead of inheritence so it can be combined with subclass of HOL (like FOL)
  this: SimpleHOLParser =>
  
  def clauseList: Parser[List[V]] = rep(clause)
  protected def clause: Parser[V]

  protected def formula2: Parser[HOLFormula] = (neg | atom)
  protected def neg2: Parser[HOLFormula] = "-" ~ atom ^^ {case "-" ~ x => Neg(x)}
  
  protected def filterPosFormulas(f: HOLFormula): Boolean = f match {
    case Neg(x) => true
    case _ => false
  }
  protected def stripNeg(f: HOLFormula): HOLFormula = f match {
    case Neg(x) => x
    case _ => f
  }
}