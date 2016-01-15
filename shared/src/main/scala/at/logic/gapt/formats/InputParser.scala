/**
 * Description:
 */

package at.logic.gapt.formats

import scala.util.parsing.combinator.RegexParsers

trait InputParser extends RegexParsers {
  def getInput(): java.io.Reader
}
