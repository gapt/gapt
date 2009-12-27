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
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.resolution.base._

trait SimpleResolutionParser extends ResolutionParser with SimpleHOLParser {
  def clauseList: Parser[List[Clause]] = rep(clause)
  def clause: Parser[Clause] = repsep(formula,"|") ~ "." ^^ {case ls ~ "." => new Clause(ls.filter(filterPosFormulas),ls.filter(x => !filterPosFormulas(x)))}

  override def formula: Parser[HOLFormula] = (atom | neg)
  override def neg: Parser[HOLFormula] = "-" ~ atom ^^ {case "-" ~ x => Neg(x)}
  
  private def filterPosFormulas(f: HOLFormula): Boolean = f match {
    case Neg(x) => true
    case _ => false
  }
}