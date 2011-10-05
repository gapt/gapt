/*
 * SimpleResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi.simple

import at.logic.language.fol.FOLFormula
import at.logic.language.hol.{Neg, HOLFormula}
import at.logic.calculi.resolution.robinson.Clause
import at.logic.parsing.calculi.ResolutionParser
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base._
import collection.immutable.Seq

import at.logic.calculi.occurrences.{factory => defaultFactory}



/*
 * In order to allow a complex inheritence structure where the resolutionParser trait is mixed
 * with HOL or FOL parsers and must override a method there on the same time we have created these
 * two helper classes.
 */
/*trait SimpleResolutionParserHOL extends SimpleResolutionParser[Clause] with SimpleFOLParser {
  override def formula = formula2
  override def neg = neg2
  def clause: Parser[Clause] = repsep(formula,"|") ~ "." ^^ {case ls ~ "." => new Clause(ls.filter(filterPosFormulas).map(stripNeg),ls.filter(x => !filterPosFormulas(x)))}
}  */
trait SimpleResolutionParserFOL extends SimpleResolutionParser with SimpleFOLParser {
  override def formula = formula2
  override def neg = neg2
  def clause: Parser[FSequent] = repsep(formula,"|") ~ "." ^^ {
      case ls ~ "." => new Pair(
            (ls.filter(filterPosFormulas).map(stripNeg)),
            (ls.filter(x => !filterPosFormulas(x)))
       ) }
}

trait SimpleResolutionParser extends ResolutionParser {
  // used instead of inheritence so it can be combined with subclass of HOL (like FOL)
  this: SimpleHOLParser =>
  
  def clauseList: Parser[List[FSequent]] = rep(clause)
  protected def clause: Parser[FSequent]

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

