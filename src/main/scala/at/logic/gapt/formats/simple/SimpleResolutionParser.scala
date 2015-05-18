/*
 * SimpleResolutionParser.scala
 *
 */

package at.logic.gapt.formats.simple

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent

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
  def clause: Parser[FSequent] = repsep( formula, "|" ) ~ "." ^^ {
    case ls ~ "." => FSequent(
      ( ls.filter( filterPosFormulas ).map( stripNeg ) ),
      ( ls.filter( x => !filterPosFormulas( x ) ) ) )
  }
}

trait SimpleResolutionParser extends ResolutionParser {
  // used instead of inheritence so it can be combined with subclass of HOL (like FOL)
  this: SimpleHOLParser =>

  def clauseList: Parser[List[FSequent]] = rep( clause )
  protected def clause: Parser[FSequent]

  protected def formula2: Parser[HOLFormula] = ( neg | atom )
  protected def neg2: Parser[HOLFormula] = "-" ~ atom ^^ { case "-" ~ x => Neg( x ) }

  protected def filterPosFormulas( f: HOLFormula ): Boolean = f match {
    case Neg( x ) => true
    case _        => false
  }
  protected def stripNeg( f: HOLFormula ): HOLFormula = f match {
    case Neg( x ) => x
    case _        => f
  }
}

