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
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.resolution.base._

/*
 * In order to allow a complex inheritence structure where the resolutionParser trait is mixed
 * with HOL or FOL parsers and must override a method there on the same time we have created these
 * two helper classes.
 */
trait SimpleResolutionParserHOL extends SimpleResolutionParser with SimpleHOLParser {
  override def formula = formula2
  override def neg = neg2
}
trait SimpleResolutionParserFOL extends SimpleResolutionParser with SimpleFOLParser {
  override def formula = formula2
  override def neg = neg2
}

trait SimpleResolutionParser extends ResolutionParser {
  // used instead of inheritence so it can be combined with subclass of HOL (like FOL)
  this: SimpleHOLParser =>
  
  def clauseList: Parser[List[Clause]] = rep(clause)
  def clause: Parser[Clause] = repsep(formula,"|") ~ "." ^^ {case ls ~ "." => new Clause(ls.filter(filterPosFormulas).map(stripNeg),ls.filter(x => !filterPosFormulas(x)))}

  protected def formula2: Parser[HOLFormula] = (atom | neg)
  protected def neg2: Parser[HOLFormula] = "-" ~ atom ^^ {case "-" ~ x => Neg(x)}
  
  private def filterPosFormulas(f: HOLFormula): Boolean = f match {
    case Neg(x) => true
    case _ => false
  }
  private def stripNeg(f: HOLFormula): HOLFormula = f match {
    case Neg(x) => x
    case _ => f
  }
}